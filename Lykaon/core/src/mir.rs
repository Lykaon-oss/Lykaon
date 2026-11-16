//! Mid-level graph (M1b), as in Chapter 67: "a mid-level graph: statements
//! become lists of steps that jump to each other". Each function is a set of
//! blocks; a block runs its steps and then jumps to a target block. Jumping
//! pops a counted number of scopes, and may push one (branches and loop
//! bodies open a fresh scope). Loop counters live in the generator state
//! (or interpreter frame), so recursion keeps separate versions of them.
//!
//! M3 completion: every sem::Stmt variant has a matching Step. Steps that
//! contain nested statements (Try, Check, Test, ForIn, ...) carry an inline
//! body so the interpreter can execute them directly; codegen lowers them to
//! runtime calls.
//!
//! The generator suspension (ch.25, M3-D12) runs the same block graph as a
//! resumable program: every step records the original sem::Stmt it came from
//! in `Block.origs`, so the interpreter executes the real statement code for
//! non-control steps and only reimplements the control flow (Branch/For*/
//! Stop/Skip/HandBack/GiveBack) that needs to suspend.

use crate::sem::E;
use crate::sem::{self, AskKind, Expr, SayMods};

#[derive(Clone, Debug)]
pub struct Target {
    pub block: usize,
    /// Scope frames to drop when jumping (or when arriving through an exit).
    pub pops: usize,
    /// Push a fresh scope when arriving (a branch body or loop body).
    pub push: bool,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub steps: Vec<Step>,
    /// The statement each step came from (1:1 with `steps`); `Stmt::Note`
    /// placeholder for control steps the executor handles natively.
    pub origs: Vec<sem::Stmt>,
    pub exit: Option<Target>,
}

#[derive(Clone, Debug)]
pub enum Step {
    Say {
        expr: Expr,
        mods: SayMods,
        newline: bool,
    },
    SayLines {
        lines: Vec<String>,
        newline: bool,
    },
    Define {
        name: String,
        eval: Expr,
        fallback: Option<Expr>,
    },
    Set {
        name: String,
        eval: Expr,
        fallback: Option<Expr>,
    },
    Ask {
        name: String,
        kind: AskKind,
        fallback: Option<Expr>,
    },
    /// The loop variable of "For each n from A to B", copied from the counter.
    DefineCounter {
        name: String,
        counter: usize,
    },
    /// cond None = always yes (Repeat forever).
    Branch {
        cond: Option<Expr>,
        yes: Option<Target>,
        no: Option<Target>,
    },
    /// Evaluates the bounds once, per invocation of the loop's function.
    ForInit {
        counter: usize,
        from: Expr,
        to: Option<Expr>,
    },
    ForCheck {
        counter: usize,
        yes: Target,
        no: Target,
    },
    Advance {
        counter: usize,
        step: i64,
        target: Target,
    },
    GiveBack {
        value: Option<Expr>,
    },
    Stop {
        pops: usize,
        target: usize,
    },
    Skip {
        pops: usize,
        target: usize,
    },
    Fail,

    // ---- M3 additions ----
    /// A local function definition inside a block: a closure (ch.24, M3-D2).
    DefineLocalFn {
        func: sem::FuncDef,
    },
    /// Hand back <value>. inside a generator function (ch.25, M3-S30).
    HandBack {
        value: Expr,
    },
    /// For each x in list/generator (ch.24, M3-S24).
    ForEach {
        var: String,
        list: Expr,
        body: Vec<sem::Stmt>,
    },
    /// Evaluate f on list / fold list with f (ch.16, M3-S22/23).
    Evaluate {
        func_ref: String,
        list: Expr,
        result_var: String,
    },
    /// Add v to the name (list).
    Append {
        value: Expr,
        list: String,
    },
    /// Put v in map under k / put v in set.
    Put {
        map: String,
        key: Option<Expr>,
        value: Expr,
    },
    /// Remove x from coll.
    Remove {
        coll: String,
        value: Expr,
    },
    /// Remove first from queue.
    RemoveFirst {
        coll: String,
    },
    /// Set part of a record value in place.
    SetPart {
        path: Vec<String>,
        expr: Expr,
    },
    /// Look at / When (ch.21).
    LookAt {
        value: Expr,
        whens: Vec<sem::When>,
    },
    /// A payment is cash or card with owner. (ch.21)
    DefineEnum {
        name: String,
        variants: Vec<(String, Vec<(String, sem::Kind)>)>,
    },
    /// Try wraps one sentence that can fail (ch.19).
    Try {
        sentence: Box<sem::Stmt>,
        success: Vec<sem::Stmt>,
        failure: Vec<(Option<String>, Vec<sem::Stmt>)>,
    },
    /// Fail with TEXT.
    FailStmt {
        message: Expr,
    },
    /// Pass failure up.
    PassFailureUp,
    /// Close x. (ch.31, can fail)
    Close {
        name: String,
    },
    /// Share <name>. (ch.36)
    Share {
        name: String,
    },
    /// Use <file>. (ch.36)
    Use {
        file: String,
    },
    /// Test <name>. block (ch.38).
    Test {
        name: String,
        body: Vec<sem::Stmt>,
    },
    /// Check that cond. / Check that this fails. / Check for any ... (ch.38).
    Check {
        text: String,
        cond: Option<Expr>,
        must_fail: bool,
        prop: Option<(String, String)>,
        body: Vec<sem::Stmt>,
    },
    /// Pretend f gives V. (ch.38)
    Pretend {
        name: String,
        value: Expr,
    },
    /// M4 (Appendix K): a sentence the graph does not analyze (channels,
    /// tasks, timers, files, formats, system, log, network): the
    /// executor runs the original statement code through exec_stmt, so
    /// a resumable body (a generator, a parked live session) runs it
    /// exactly like the eager interpreter does.
    Other,
}

#[derive(Debug)]
pub struct FnMir {
    pub name: String,
    pub inputs: Vec<String>,
    pub entry: usize,
}

#[derive(Debug)]
pub struct ProgramMir {
    pub blocks: Vec<Block>,
    pub entry: usize,
    pub funcs: Vec<FnMir>,
    /// How many loop counters the graph allocates (indices into the
    /// generator's counter list).
    pub counter_count: usize,
}

/// Bookkeeping for the Stop. and Skip. words: where they must jump, and how
/// many scopes they must drop to get there (one per loop body plus one per
/// open If branch inside it).
#[derive(Clone, Copy)]
pub struct InnerLoop {
    pub stop: usize,
    pub skip: usize,
    pub pops: usize,
}

pub fn build(p: &sem::Program) -> ProgramMir {
    let mut m = MB {
        blocks: Vec::new(),
        counters: 0,
    };
    let (entry, _) = m.stmts(&p.body, None);
    let mut funcs = Vec::new();
    for f in &p.funcs {
        let (fentry, _) = m.fn_body(f);
        funcs.push(FnMir {
            name: f.name.clone(),
            inputs: f.inputs.iter().map(|(n, _)| n.clone()).collect(),
            entry: fentry,
        });
    }
    ProgramMir {
        blocks: m.blocks,
        entry,
        funcs,
        counter_count: m.counters,
    }
}

/// Build the block graph of one function alone (used by generator suspension,
/// ch.25): the blocks are self-contained and `entry` is where the body starts.
pub fn build_fn_body(f: &sem::FuncDef) -> (ProgramMir, usize) {
    let mut m = MB {
        blocks: Vec::new(),
        counters: 0,
    };
    let (entry, _) = m.fn_body(f);
    let mir = ProgramMir {
        blocks: m.blocks,
        entry,
        funcs: Vec::new(),
        counter_count: m.counters,
    };
    (mir, entry)
}

/// Build the block graph of one statement list alone (used by the live
/// session executor, M4-S73/D13 route A): the blocks are self-contained
/// and `entry` is where the list starts.
pub fn build_stmts(stmts: &[sem::Stmt]) -> (ProgramMir, usize) {
    let mut m = MB {
        blocks: Vec::new(),
        counters: 0,
    };
    let (entry, _) = m.stmts(stmts, None);
    let mir = ProgramMir {
        blocks: m.blocks,
        entry,
        funcs: Vec::new(),
        counter_count: m.counters,
    };
    (mir, entry)
}

struct MB {
    blocks: Vec<Block>,
    counters: usize,
}

impl MB {
    fn new_block(&mut self) -> usize {
        self.blocks.push(Block {
            steps: Vec::new(),
            origs: Vec::new(),
            exit: None,
        });
        self.blocks.len() - 1
    }

    /// Push one step together with the statement it came from, so the
    /// executor can run the real statement code (ch.25 suspension).
    fn push_step(&mut self, blk: usize, s: Step, orig: Option<&sem::Stmt>) {
        self.blocks[blk].steps.push(s);
        self.blocks[blk]
            .origs
            .push(orig.cloned().unwrap_or(sem::Stmt::Note));
    }

    fn fn_body(&mut self, f: &sem::FuncDef) -> (usize, usize) {
        match &f.body {
            sem::FnBody::Expr(e) => {
                let b = self.new_block();
                self.push_step(
                    b,
                    Step::GiveBack {
                        value: Some(e.clone()),
                    },
                    None,
                );
                (b, b)
            }
            sem::FnBody::Block(stmts) => self.stmts(stmts, None),
        }
    }

    fn whole_lit(v: i64) -> Expr {
        Expr {
            kind: sem::Kind::Whole,
            e: E::Whole(v),
            dis: String::new(),
            can_fail: false,
            num_word: false,
        }
    }

    /// Build a statement list; returns (entry block, last block of the list).
    fn stmts(&mut self, stmts: &[sem::Stmt], inner: Option<InnerLoop>) -> (usize, usize) {
        let entry = self.new_block();
        let mut cur = entry;
        for st in stmts {
            match st {
                // ---- M4 (Appendix K) task/timer/channel/file/format/
                // system/log/network sentences are not part of the M3
                // prover's block graph analysis (the prover sees nothing
                // through them: nothing is recorded for their contracts,
                // so every check stays an unknown live check -
                // conservative by design). They still RUN in a resumable
                // body: each is recorded as Step::Other and the executor
                // runs the original statement code (M4-S73/D13).
                sem::Stmt::StartTask { .. }
                | sem::Stmt::WaitFor { .. }
                | sem::Stmt::DoTogether { .. }
                | sem::Stmt::StopTask { .. }
                | sem::Stmt::SleepFor { .. }
                | sem::Stmt::Send { .. }
                | sem::Stmt::Receive { .. }
                | sem::Stmt::AtomicAdd { .. }
                | sem::Stmt::AfterTimer { .. }
                | sem::Stmt::EveryTimer { .. }
                | sem::Stmt::StreamLoop { .. }
                | sem::Stmt::UseWorkers { .. }
                | sem::Stmt::Spread { .. } => {
                    self.push_step(cur, Step::Other, Some(st));
                }
                // M4-5 (7.5): the file sentences run through the evaluator;
                // each still runs in a resumable body (Step::Other)
                sem::Stmt::ReadFile { .. }
                | sem::Stmt::ReadBytes { .. }
                | sem::Stmt::WriteFile { .. }
                | sem::Stmt::AppendFile { .. }
                | sem::Stmt::ReplaceFile { .. }
                | sem::Stmt::ForEachLine { .. }
                | sem::Stmt::MakeFolder { .. }
                | sem::Stmt::RemovePath { .. }
                | sem::Stmt::MovePath { .. }
                | sem::Stmt::DuplicatePath { .. }
                | sem::Stmt::ListFolder { .. }
                | sem::Stmt::MakeTempFile { .. }
                | sem::Stmt::WhenFileChanges { .. }
                | sem::Stmt::ZipOp { .. } => {
                    self.push_step(cur, Step::Other, Some(st));
                }
                // M4-6 (7.6): the format sentences run through the
                // evaluator; each still runs in a resumable body
                sem::Stmt::ReadFormat { .. }
                | sem::Stmt::ReadFormatText { .. }
                | sem::Stmt::SaveFormat { .. } => {
                    self.push_step(cur, Step::Other, Some(st));
                }
                // M4-7 (7.7): Use seed runs through the evaluator and
                // records nothing
                sem::Stmt::UseSeed { .. } => {
                    self.push_step(cur, Step::Other, Some(st));
                }
                // M4-8 (7.10/7.11): the system and tool sentences run
                // through the evaluator (Run spawns another program; Exit
                // ends it; the signal block is a task outside the graph;
                // the input loops stream); each still runs in a resumable
                // body
                sem::Stmt::RunProc { .. }
                | sem::Stmt::Exit { .. }
                | sem::Stmt::WhenSignal { .. }
                | sem::Stmt::ForEachInput { .. }
                // M4-9 (7.12): Log and Use log level run through the
                // evaluator (they touch the run's log level and streams)
                | sem::Stmt::Log { .. }
                | sem::Stmt::LogLevel { .. } => {
                    self.push_step(cur, Step::Other, Some(st));
                }
                // M4-10 (7.8): the network sentences run through the
                // evaluator (Fetch blocks on the socket; the handler
                // bodies are evaluator-run tasks); each still runs in a
                // resumable body - Send/Receive/WsSend/WsRecv are the
                // live session's suspension points
                sem::Stmt::Fetch { .. }
                | sem::Stmt::PostTo { .. }
                | sem::Stmt::Serve { .. }
                | sem::Stmt::WhenSomeone { .. }
                | sem::Stmt::WhenLive { .. }
                | sem::Stmt::Respond { .. }
                | sem::Stmt::PageDecl { .. }
                | sem::Stmt::WsSend { .. }
                | sem::Stmt::WsRecv { .. }
                | sem::Stmt::Careful { .. } => {
                    self.push_step(cur, Step::Other, Some(st));
                }
                sem::Stmt::Note => {}
                sem::Stmt::HandBack(e) => {
                    self.push_step(cur, Step::HandBack { value: e.clone() }, Some(st));
                }
                sem::Stmt::DefineLocalFn(f) => {
                    self.push_step(cur, Step::DefineLocalFn { func: f.clone() }, Some(st));
                }
                // M1b list / pronoun sentences are executed by the interpreter
                // walking the typed tree; the block graph records them as notes.
                sem::Stmt::ForIn { vars, list, body } => {
                    self.push_step(cur, Step::ForEach {
                        var: vars.first().cloned().unwrap_or_default(),
                        list: list.clone(),
                        body: body.clone(),
                    }, Some(st));
                }
                sem::Stmt::Evaluate { expr, list } => {
                    let func_ref = match &expr.e {
                        sem::E::Name(n) => n.clone(),
                        _ => "unknown".to_string(),
                    };
                    self.push_step(cur, Step::Evaluate {
                        func_ref,
                        list: Expr { kind: sem::Kind::Whole, e: E::Whole(if *list { 1 } else { 0 }), dis: String::new(), can_fail: false, num_word: false },
                        result_var: "it".to_string(),
                    }, Some(st));
                }
                sem::Stmt::Append { value, list } => {
                    self.push_step(cur, Step::Append { value: value.clone(), list: list.clone() }, Some(st));
                }
                sem::Stmt::Put { map, key, value } => {
                    self.push_step(cur, Step::Put { map: map.clone(), key: key.clone(), value: value.clone() }, Some(st));
                }
                sem::Stmt::Remove { coll, value } => {
                    self.push_step(cur, Step::Remove { coll: coll.clone(), value: value.clone() }, Some(st));
                }
                sem::Stmt::RemoveFirst { coll } => {
                    self.push_step(cur, Step::RemoveFirst { coll: coll.clone() }, Some(st));
                }
                sem::Stmt::SetPart { path, expr } => {
                    self.push_step(cur, Step::SetPart { path: path.clone(), expr: expr.clone() }, Some(st));
                }
                sem::Stmt::LookAt { value, whens } => {
                    self.push_step(cur, Step::LookAt { value: value.clone(), whens: whens.clone() }, Some(st));
                }
                sem::Stmt::DefineEnum { name, variants } => {
                    self.push_step(cur, Step::DefineEnum { name: name.clone(), variants: variants.clone() }, Some(st));
                }
                sem::Stmt::Try { sentence, success, failure } => {
                    self.push_step(cur, Step::Try {
                        sentence: sentence.clone(),
                        success: success.clone(),
                        failure: failure.clone(),
                    }, Some(st));
                }
                sem::Stmt::Fail { message } => {
                    self.push_step(cur, Step::FailStmt { message: message.clone() }, Some(st));
                }
                sem::Stmt::PassFailureUp => {
                    self.push_step(cur, Step::PassFailureUp, Some(st));
                }
                sem::Stmt::Close { name } => {
                    self.push_step(cur, Step::Close { name: name.clone() }, Some(st));
                }
                sem::Stmt::Share { name } => {
                    self.push_step(cur, Step::Share { name: name.clone() }, Some(st));
                }
                sem::Stmt::Use { file } => {
                    self.push_step(cur, Step::Use { file: file.clone() }, Some(st));
                }
                sem::Stmt::Test { name, body } => {
                    self.push_step(cur, Step::Test { name: name.clone(), body: body.clone() }, Some(st));
                }
                sem::Stmt::Check { text, cond, must_fail, prop, body } => {
                    self.push_step(cur, Step::Check {
                        text: text.clone(),
                        cond: cond.clone(),
                        must_fail: *must_fail,
                        prop: prop.clone(),
                        body: body.clone(),
                    }, Some(st));
                }
                sem::Stmt::Pretend { name, value } => {
                    self.push_step(cur, Step::Pretend { name: name.clone(), value: value.clone() }, Some(st));
                }
                sem::Stmt::Say { expr, mods, lines } => {
                    let newline = !mods.without_newline;
                    let empty_flat = matches!(&expr.e, sem::E::Flat(v) if v.is_empty());
                    if !lines.is_empty() && empty_flat {
                        self.push_step(cur, Step::SayLines { lines: lines.clone(), newline }, Some(st));
                    } else {
                        self.push_step(cur, Step::Say { expr: expr.clone(), mods: mods.clone(), newline }, Some(st));
                    }
                }
                sem::Stmt::Define(d) => {
                    self.push_step(cur, Step::Define {
                        name: d.name.clone(), eval: d.expr.clone(), fallback: d.fallback.clone(),
                    }, Some(st));
                }
                sem::Stmt::Set { name, expr } => {
                    self.push_step(cur, Step::Set {
                        name: name.clone(), eval: expr.clone(), fallback: None,
                    }, Some(st));
                }
                sem::Stmt::Ask { name, kind, fallback } => {
                    self.push_step(cur, Step::Ask {
                        name: name.clone(), kind: *kind, fallback: fallback.clone(),
                    }, Some(st));
                }
                sem::Stmt::Stop => match inner {
                    Some(l) => {
                        self.push_step(cur, Step::Stop { pops: l.pops, target: l.stop }, None);
                        cur = self.new_block(); // the rest of the block is not reached
                    }
                    None => {} // the syntax layer already reported T0113
                },
                sem::Stmt::Skip => match inner {
                    Some(l) => {
                        self.push_step(cur, Step::Skip { pops: l.pops, target: l.skip }, None);
                        cur = self.new_block();
                    }
                    None => {}
                },
                sem::Stmt::GiveBack(v) => {
                    self.push_step(cur, Step::GiveBack { value: v.clone() }, None);
                    cur = self.new_block();
                }
                sem::Stmt::If { branches, other } => {
                    let innerp = inner.map(|l| InnerLoop { pops: l.pops + 1, ..l });
                    let after = self.new_block();
                    let n = branches.len();
                    let mut cond_blocks: Vec<usize> = Vec::new();
                    for _ in 0..n {
                        cond_blocks.push(self.new_block());
                    }
                    let mut yes_blocks = Vec::new();
                    for (_, body) in branches.iter() {
                        let (be, bl) = self.stmts(body, innerp);
                        self.blocks[bl].exit = Some(Target { block: after, pops: 1, push: false });
                        yes_blocks.push(be);
                    }
                    let other_entry = other.as_ref().map(|ob| {
                        let (oe, ol) = self.stmts(ob, innerp);
                        self.blocks[ol].exit = Some(Target { block: after, pops: 1, push: false });
                        oe
                    });
                    for i in 0..n {
                        let (cond, _) = &branches[i];
                        let no = if i + 1 < n {
                            Some(Target { block: cond_blocks[i + 1], pops: 0, push: false })
                        } else if let Some(oe) = other_entry {
                            Some(Target { block: oe, pops: 0, push: true })
                        } else {
                            Some(Target { block: after, pops: 0, push: false })
                        };
                        self.push_step(cond_blocks[i], Step::Branch {
                            cond: Some(cond.clone()),
                            yes: Some(Target { block: yes_blocks[i], pops: 0, push: true }),
                            no,
                        }, None);
                    }
                    self.blocks[cur].exit = Some(Target { block: cond_blocks[0], pops: 0, push: false });
                    cur = after;
                }
                sem::Stmt::RepeatTimes { count, body } => {
                    let id = self.counters;
                    self.counters += 1;
                    let after = self.new_block();
                    let check = self.new_block();
                    let adv = self.new_block();
                    let (bentry, blast) = self.stmts(body, Some(InnerLoop {
                        stop: after, skip: adv, pops: 1,
                    }));
                    self.blocks[blast].exit = Some(Target { block: adv, pops: 1, push: false });
                    self.push_step(adv, Step::Advance {
                        counter: id, step: 1, target: Target { block: check, pops: 0, push: false },
                    }, None);
                    self.push_step(check, Step::ForInit {
                        counter: id, from: Self::whole_lit(1), to: Some(count.clone()),
                    }, None);
                    self.push_step(check, Step::ForCheck {
                        counter: id,
                        yes: Target { block: bentry, pops: 0, push: true },
                        no: Target { block: after, pops: 0, push: false },
                    }, None);
                    self.blocks[cur].exit = Some(Target { block: check, pops: 0, push: false });
                    cur = after;
                }
                sem::Stmt::RepeatForever { body } => {
                    let after = self.new_block();
                    let check = self.new_block();
                    let (bentry, blast) = self.stmts(body, Some(InnerLoop {
                        stop: after, skip: check, pops: 1,
                    }));
                    self.blocks[blast].exit = Some(Target { block: check, pops: 1, push: false });
                    self.push_step(check, Step::Branch {
                        cond: None,
                        yes: Some(Target { block: bentry, pops: 0, push: true }),
                        no: Some(Target { block: after, pops: 0, push: false }),
                    }, None);
                    self.blocks[cur].exit = Some(Target { block: check, pops: 0, push: false });
                    cur = after;
                }
                sem::Stmt::RepeatWhile { cond, body } => {
                    let after = self.new_block();
                    let check = self.new_block();
                    let (bentry, blast) = self.stmts(body, Some(InnerLoop {
                        stop: after, skip: check, pops: 1,
                    }));
                    self.blocks[blast].exit = Some(Target { block: check, pops: 1, push: false });
                    self.push_step(check, Step::Branch {
                        cond: Some(cond.clone()),
                        yes: Some(Target { block: bentry, pops: 0, push: true }),
                        no: Some(Target { block: after, pops: 0, push: false }),
                    }, None);
                    self.blocks[cur].exit = Some(Target { block: check, pops: 0, push: false });
                    cur = after;
                }
                sem::Stmt::ForRange { var, from, to, body } => {
                    let id = self.counters;
                    self.counters += 1;
                    let after = self.new_block();
                    let check = self.new_block();
                    let adv = self.new_block();
                    let (bentry, blast) = self.stmts(body, Some(InnerLoop {
                        stop: after, skip: adv, pops: 1,
                    }));
                    self.blocks[blast].exit = Some(Target { block: adv, pops: 1, push: false });
                    self.push_step(adv, Step::Advance {
                        counter: id, step: 1, target: Target { block: check, pops: 0, push: false },
                    }, None);
                    self.blocks[bentry].steps.insert(0, Step::DefineCounter {
                        name: var.clone(), counter: id,
                    });
                    self.blocks[bentry].origs.insert(0, sem::Stmt::Note);
                    self.blocks[check].steps.push(Step::ForInit {
                        counter: id, from: from.clone(), to: Some(to.clone()),
                    });
                    self.blocks[check].origs.push(sem::Stmt::Note);
                    self.blocks[check].steps.push(Step::ForCheck {
                        counter: id,
                        yes: Target { block: bentry, pops: 0, push: true },
                        no: Target { block: after, pops: 0, push: false },
                    });
                    self.blocks[check].origs.push(sem::Stmt::Note);
                    self.blocks[cur].exit = Some(Target { block: check, pops: 0, push: false });
                    cur = after;
                }
            }
        }
        (entry, cur)
    }
}
