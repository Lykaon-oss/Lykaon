//! Optimizer passes for Lykaon M3 (book section 12 / M3-D5).
//!
//! The passes run on the typed tree (`sem::Program`) in place, so both
//! runners — the interpreter and the native code generator — can take the
//! optimized program and the differential rule (native == interpreter byte
//! for byte) stays intact by construction:
//!
//!   1. Constant folding: literal arithmetic the running program would
//!      redo. Only exact rules fold; anything that could change an answer
//!      (a checked overflow, a division that fails, a minus past the
//!      lowest number) is left alone for the running program to handle.
//!   2. Unreachable-statement removal: statements after a give back are
//!      dead (the interpreter returns early there).
//!   3. Unused-name removal: a defined name no statement ever reads, when
//!      its right-hand side is side-effect free.
//!   4. Inlining: a function whose body is a single give back whose
//!      expression holds no calls or pronouns and mentions no name beyond
//!      its own inputs, is substituted at its call sites. Argument kinds
//!      are already known (M3-S9), so the substituted body behaves exactly
//!      like the call did.
//!   5. Tail-call marking: `give back <name> ...` self-calls are counted
//!      and reported. No code change: the running depth limit (T0607)
//!      must stay observable, so a loop conversion would break it.
//!
//! Bounds-check elimination is REAL for provable literal-list accesses (see
//! prove_literal_index), and devirtualization now rewrites interface calls
//! whose receiver kind is known statically to a direct call (see
//! devirtualize below); lists and interface dispatch whose kinds stay
//! unknown at compile time run through the evaluator, which is where the
//! M7 lowering work continues.

use crate::sem::{self, E, Expr, Kind, Op, Program, Stmt};
use std::collections::{HashMap, HashSet};

/// One pass report: how many places the pass rewrote.
#[derive(Clone, Debug)]
pub struct PassReport {
    pub name: &'static str,
    pub changes: usize,
}

/// Run every pass in order. `mode` selects how much runs: "debug" keeps
/// the freshly compiled tree untouched; "fast" and "small" apply all of
/// the safe passes (M3-D6).
pub fn optimize_tree(prog: &mut Program, mode: &str) -> Vec<PassReport> {
    let mut reports = Vec::new();
    // The contract prover only READS the tree (it decides which Ensures
    // checks are provably always true), so it runs in every mode including
    // debug — a proven check is skipped at run time in all modes (M3b-1).
    reports.push(PassReport {
        name: "contract prover",
        changes: crate::prover::checks_removed(prog),
    });
    if mode == "debug" {
        return reports;
    }
    let folded = fold_program(prog);
    reports.push(PassReport {
        name: "constant folding",
        changes: folded,
    });
    let unreachable = drop_unreachable(prog);
    reports.push(PassReport {
        name: "unreachable code",
        changes: unreachable,
    });
    let unused = drop_unused_names(prog);
    reports.push(PassReport {
        name: "unused names",
        changes: unused,
    });
    let aligned = inline_calls(prog);
    reports.push(PassReport {
        name: "inlining",
        changes: aligned,
    });
    // M3c-2 whole-program block-body inlining: multi-statement pure
    // bodies (local Sets + one give back) spliced at their call sites.
    let blocks = crate::wpo::inline_block_bodies(prog);
    reports.push(PassReport {
        name: "whole-program inlining",
        changes: blocks,
    });
    let tails = mark_tail_calls(prog);
    reports.push(PassReport {
        name: "tail calls marked",
        changes: tails,
    });
    let bounds = eliminate_bounds_checks(prog);
    reports.push(PassReport {
        name: "bounds-check elimination",
        changes: bounds,
    });
    let devirt = devirtualize(prog);
    reports.push(PassReport {
        name: "devirtualization",
        changes: devirt,
    });
    // M3c-3 cross-package constant propagation: top-level immutable
    // values (Constant / plain `name is value.`) with leaf literals
    // replace their later name reads (statement order respected).
    let consts = crate::wpo::propagate_constants(prog);
    reports.push(PassReport {
        name: "cross-package constants",
        changes: consts,
    });
    let dead = crate::wpo::remove_dead_funcs(prog);
    reports.push(PassReport {
        name: "whole-program dead functions",
        changes: dead,
    });
    reports
}

// =============================================== statement-list walking

/// Run `cb` over every statement list of the program: the top-level body,
/// every function and implementation body, every test body, and every
/// list nested inside them (branches, loop bodies, Try arms, Look at
/// arms, Check bodies, local function bodies).
pub(crate) fn every_list(prog: &mut Program, cb: &mut dyn FnMut(&mut Vec<Stmt>)) {
    fn go_all(prog: &mut Program, cb: &mut dyn FnMut(&mut Vec<Stmt>)) {
        helper_walk_list(&mut prog.body, cb);
        for f in &mut prog.funcs {
            if let sem::FnBody::Block(s) = &mut f.body {
                helper_walk_list(s, cb);
            }
        }
        for imp in &mut prog.impls {
            for f in &mut imp.funcs {
                if let sem::FnBody::Block(s) = &mut f.body {
                    helper_walk_list(s, cb);
                }
            }
            helper_walk_list(&mut imp.body, cb);
        }
        for t in &mut prog.tests {
            helper_walk_list(&mut t.body, cb);
        }
    }
    go_all(prog, cb);
}

fn helper_walk_list(list: &mut Vec<Stmt>, cb: &mut dyn FnMut(&mut Vec<Stmt>)) {
    cb(list);
    for st in list.iter_mut() {
        helper_walk_stmt_lists(st, cb);
    }
}

fn helper_walk_stmt_lists(st: &mut Stmt, cb: &mut dyn FnMut(&mut Vec<Stmt>)) {
    match st {
        Stmt::Note
        | Stmt::Stop
        | Stmt::Skip
        | Stmt::PassFailureUp
        | Stmt::Share { .. }
        | Stmt::Use { .. }
        | Stmt::Close { .. }
        | Stmt::RemoveFirst { .. }
        | Stmt::DefineEnum { .. }
        | Stmt::Define(_)
        | Stmt::Set { .. }
        | Stmt::Say { .. }
        | Stmt::Ask { .. }
        | Stmt::Evaluate { .. }
        | Stmt::Append { .. }
        | Stmt::Put { .. }
        | Stmt::Remove { .. }
        | Stmt::SetPart { .. }
        | Stmt::Fail { .. }
        | Stmt::Pretend { .. }
        | Stmt::GiveBack(_)
        | Stmt::HandBack(_) => {}
        // M4 (Appendix K): Send/Receive/AtomicAdd carry no blocks
        Stmt::Send { .. } | Stmt::Receive { .. } | Stmt::AtomicAdd { .. } => {}
        // M4-5 (Appendix K 7.5): the file sentences carry no block except
        // the for-each-line / when-file-changes bodies
        Stmt::ReadFile { .. }
        | Stmt::ReadBytes { .. }
        | Stmt::WriteFile { .. }
        | Stmt::AppendFile { .. }
        | Stmt::ReplaceFile { .. }
        | Stmt::MakeFolder { .. }
        | Stmt::RemovePath { .. }
        | Stmt::MovePath { .. }
        | Stmt::DuplicatePath { .. }
        | Stmt::ListFolder { .. }
        | Stmt::MakeTempFile { .. }
        | Stmt::ZipOp { .. }
        | Stmt::ReadFormat { .. }
        | Stmt::ReadFormatText { .. }
        | Stmt::SaveFormat { .. } => {}
        // M4-7 (7.7): Use seed carries no body.
        Stmt::UseSeed { .. } => {}
        // M4-8 (7.10/7.11): the signal and input loop bodies are statement
        // lists; Run/Exit carry none
        Stmt::RunProc { .. } | Stmt::Exit { .. } => {}
        // M4-9 (7.12): the Log text is walked by the expression walker;
        // Use log level carries no body
        Stmt::Log { .. } | Stmt::LogLevel { .. } => {}
        // M4-10 (7.8): the network sentences carry no statement bodies
        // except the Serve/handler blocks, which are statement lists
        // (their expressions go through the expression walker)
        Stmt::Serve { body, .. } | Stmt::WhenSomeone { body, .. } | Stmt::WhenLive { body, .. } => {
            helper_walk_list(body, cb);
        }
        Stmt::Fetch { .. }
        | Stmt::PostTo { .. }
        | Stmt::Respond { .. }
        | Stmt::PageDecl { .. }
        | Stmt::WsSend { .. }
        | Stmt::WsRecv { .. } => {}
        Stmt::Careful { body } => helper_walk_list(body, cb),
        Stmt::WhenSignal { body, .. } | Stmt::ForEachInput { body, .. } => {
            helper_walk_list(body, cb);
        }
        Stmt::ForEachLine { body, .. } | Stmt::WhenFileChanges { body, .. } => {
            helper_walk_list(body, cb);
        }
        Stmt::If { branches, other } => {
            for (_, body) in branches.iter_mut() {
                helper_walk_list(body, cb);
            }
            if let Some(ob) = other {
                helper_walk_list(ob, cb);
            }
        }
        Stmt::RepeatTimes { body, .. }
        | Stmt::RepeatForever { body }
        | Stmt::RepeatWhile { body, .. }
        | Stmt::ForRange { body, .. }
        | Stmt::ForIn { body, .. }
        | Stmt::Test { body, .. }
        | Stmt::Check { body, .. } => helper_walk_list(body, cb),
        Stmt::LookAt { whens, .. } => {
            for w in whens.iter_mut() {
                helper_walk_list(&mut w.body, cb);
            }
        }
        Stmt::Try {
            sentence,
            success,
            failure,
        } => {
            helper_walk_stmt_lists(sentence, cb);
            helper_walk_list(success, cb);
            for (_, arms) in failure.iter_mut() {
                helper_walk_list(arms, cb);
            }
        }
        Stmt::DefineLocalFn(f) => {
            if let sem::FnBody::Block(s) = &mut f.body {
                helper_walk_list(s, cb);
            }
        }
        // M4 (Appendix K): task bodies are statement lists the helpers
        // walk too (they can call functions); Do these together is one.
        Stmt::StartTask { body, .. } | Stmt::DoTogether { body } => helper_walk_list(body, cb),
        Stmt::WaitFor { .. } | Stmt::StopTask { .. } | Stmt::SleepFor { .. } => {}
        // M4-4 (Appendix K 7.3/7.4): timer, stream and spread bodies are
        // statement lists too.
        Stmt::AfterTimer { body, .. }
        | Stmt::EveryTimer { body, .. }
        | Stmt::StreamLoop { body, .. }
        | Stmt::Spread { body, .. } => helper_walk_list(body, cb),
        Stmt::UseWorkers { .. } => {}
    }
}

/// Mutable visit of every expression the statement holds, in place.
pub(crate) fn map_stmt_exprs(st: &mut Stmt, f: &mut dyn FnMut(&mut Expr)) {
    fn go_list(list: &mut [Stmt], f: &mut dyn FnMut(&mut Expr)) {
        for st in list.iter_mut() {
            map_stmt_exprs(st, f);
        }
    }
    match st {
        Stmt::Note | Stmt::Stop | Stmt::Skip | Stmt::PassFailureUp
        | Stmt::Share { .. } | Stmt::Use { .. } | Stmt::Close { .. }
        | Stmt::RemoveFirst { .. } | Stmt::DefineEnum { .. } => {}
        // M4 (Appendix K) task sentences hold no expressions of their own.
        Stmt::StartTask { .. } | Stmt::WaitFor { .. } | Stmt::DoTogether { .. }
        | Stmt::StopTask { .. } | Stmt::SleepFor { .. }
        // M4-4: Use N workers. carries only the count literal.
        | Stmt::UseWorkers { .. }
        // M4-7: Use seed. carries only the seed literal.
        | Stmt::UseSeed { .. }
        // M4-8 (7.10/7.11): Exit carries only a literal code; Receive holds
        // only the channel name
        | Stmt::Receive { .. } => {}
        // M4-8 (7.10/7.11): the Run arguments and the signal/input loop
        // bodies hold expressions of the enclosing context.
        Stmt::RunProc { args, .. } => {
            for a in args.iter_mut() {
                f(a);
            }
        }
        Stmt::Exit { .. } => {}
        // M4-9 (7.12): the Log text is an expression of the enclosing
        // context (like a Say's)
        Stmt::Log { expr, .. } => f(expr),
        Stmt::LogLevel { .. } => {}
        // M4-10 (7.8): the fetch/post data, header and query values are
        // expressions of the enclosing context; a Send frame value too
        Stmt::Fetch { data, headers, query, .. } => {
            if let Some(d) = data {
                f(d);
            }
            for (_, e) in headers.iter_mut().chain(query.iter_mut()) {
                f(e);
            }
        }
        Stmt::PostTo { data, .. } => f(data),
        Stmt::WsSend { value } => f(value),
        // the handler bodies' expressions walk (they run in the
        // enclosing context through the eager model)
        Stmt::Serve { body, .. } | Stmt::WhenSomeone { body, .. }
        | Stmt::WhenLive { body, .. } => go_list(body, f),
        Stmt::Respond { kind, .. } => match kind {
            sem::RespondKind::Text(e) | sem::RespondKind::Json(e)
            | sem::RespondKind::Literally(e) => f(e),
            sem::RespondKind::Status(_, Some(e)) => f(e),
            sem::RespondKind::Status(_, None) | sem::RespondKind::Template(_) => {}
        },
        Stmt::PageDecl { .. } | Stmt::WsRecv { .. } => {}
        Stmt::Careful { body } => go_list(body, f),
        Stmt::WhenSignal { body, .. } | Stmt::ForEachInput { body, .. } => go_list(body, f),
        // M4 (Appendix K): Send/AtomicAdd carry the value expression
        Stmt::Send { value, .. } | Stmt::AtomicAdd { value, .. } => f(value),
        // M4-4 (Appendix K 7.3/7.4): timer, stream and spread bodies walk;
        // the spread items value is an expression of the enclosing context.
        Stmt::AfterTimer { body, .. } | Stmt::EveryTimer { body, .. }
        | Stmt::StreamLoop { body, .. } => go_list(body, f),
        Stmt::Spread { items, body } => {
            f(items);
            go_list(body, f);
        }
        // M4-5 (Appendix K 7.5): the write/append/replace value is an
        // expression; the for-each-line / when-file-changes bodies walk.
        Stmt::WriteFile { value, .. } | Stmt::AppendFile { value, .. }
        | Stmt::ReplaceFile { value, .. }
        | Stmt::SaveFormat { value, .. } | Stmt::ReadFormatText { value, .. } => f(value),
        Stmt::ReadFile { .. } | Stmt::ReadBytes { .. } | Stmt::ListFolder { .. }
        | Stmt::MakeFolder { .. } | Stmt::RemovePath { .. } | Stmt::MovePath { .. }
        | Stmt::DuplicatePath { .. } | Stmt::MakeTempFile { .. }
        | Stmt::ZipOp { .. } | Stmt::ReadFormat { .. } => {}
        Stmt::ForEachLine { body, .. } | Stmt::WhenFileChanges { body, .. } => {
            go_list(body, f)
        }
        Stmt::Define(d) => {
            f(&mut d.expr);
            if let Some(fb) = &mut d.fallback {
                f(fb);
            }
        }
        Stmt::Set { expr, .. } => f(expr),
        Stmt::Say { expr, .. } => f(expr),
        Stmt::Ask { fallback, .. } => {
            if let Some(e) = fallback {
                f(e);
            }
        }
        Stmt::If { branches, other } => {
            for (cond, body) in branches.iter_mut() {
                f(cond);
                go_list(body, f);
            }
            if let Some(ob) = other {
                go_list(ob, f);
            }
        }
        Stmt::RepeatTimes { count, body } => {
            f(count);
            go_list(body, f);
        }
        Stmt::RepeatForever { body } => go_list(body, f),
        Stmt::RepeatWhile { cond, body } => {
            f(cond);
            go_list(body, f);
        }
        Stmt::ForRange { from, to, body, .. } => {
            f(from);
            f(to);
            go_list(body, f);
        }
        Stmt::ForIn { list, body, .. } => {
            f(list);
            go_list(body, f);
        }
        Stmt::Evaluate { expr, .. } => f(expr),
        Stmt::Append { value, .. } => f(value),
        Stmt::Put { key, value, .. } => {
            if let Some(k) = key {
                f(k);
            }
            f(value);
        }
        Stmt::Remove { value, .. } => f(value),
        Stmt::SetPart { expr, .. } => f(expr),
        Stmt::LookAt { value, whens } => {
            f(value);
            for w in whens.iter_mut() {
                go_list(&mut w.body, f);
            }
        }
        Stmt::Try { sentence, success, failure } => {
            map_stmt_exprs(sentence, f);
            go_list(success, f);
            for (_, arms) in failure.iter_mut() {
                go_list(arms, f);
            }
        }
        Stmt::Fail { message } => f(message),
        Stmt::Test { body, .. } => go_list(body, f),
        Stmt::Check { cond, body, .. } => {
            if let Some(c) = cond {
                f(c);
            }
            go_list(body, f);
        }
        Stmt::Pretend { value, .. } => f(value),
        Stmt::GiveBack(e) => {
            if let Some(e) = e {
                f(e);
            }
        }
        Stmt::HandBack(e) => f(e),
        Stmt::DefineLocalFn(fbody) => match &mut fbody.body {
            sem::FnBody::Block(s) => go_list(s, f),
            sem::FnBody::Expr(e) => f(e),
        },
    }
}

// ============================================================ fold pass

fn fold_program(prog: &mut Program) -> usize {
    let mut folded = 0;
    every_list(prog, &mut |list| {
        for st in list.iter_mut() {
            folded += fold_stmt(st);
        }
    });
    // one-line function bodies hold no statement list of their own
    for f in &mut prog.funcs {
        if let sem::FnBody::Expr(e) = &mut f.body {
            folded += fold_expr(e) as usize;
        }
    }
    for imp in &mut prog.impls {
        for f in &mut imp.funcs {
            if let sem::FnBody::Expr(e) = &mut f.body {
                folded += fold_expr(e) as usize;
            }
        }
    }
    folded
}

fn fold_stmt(st: &mut Stmt) -> usize {
    let mut folded = 0;
    map_stmt_exprs(st, &mut |e| {
        folded += fold_expr(e) as usize;
    });
    folded
}

/// Fold one expression in place; true when the node (or a child) changed.
fn fold_expr(e: &mut Expr) -> bool {
    let mut folded = false;
    for child in children_mut(e) {
        folded |= fold_expr(child);
    }
    folded |= fold_value(e);
    folded
}

/// The exact arithmetic of the built-ins, applied early: checked
/// operations that would overflow keep that overflow for the running
/// program; decimal results are the same IEEE sums, products, and
/// quotients the running program would compute.
fn fold_value(e: &mut Expr) -> bool {
    let original_kind = e.kind.clone();
    match &e.e {
        E::Binary { op, l, r } => {
            // whole/whole arithmetic, exactly as bin_op runs it
            if let (E::Whole(a), E::Whole(b)) = (&l.e, &r.e) {
                let pick = match op {
                    Op::Plus => a.checked_add(*b),
                    Op::Minus => a.checked_sub(*b),
                    Op::Time => a.checked_mul(*b),
                    // a checked overflow must still reach its running
                    // signal, so an overflowing fold is skipped
                    Op::CheckedPlus => a.checked_add(*b),
                    Op::CheckedMinus => a.checked_sub(*b),
                    Op::CheckedTimes => a.checked_mul(*b),
                    Op::WrappingPlus => Some(a.wrapping_add(*b)),
                    Op::WrappingMinus => Some(a.wrapping_sub(*b)),
                    Op::WrappingTimes => Some(a.wrapping_mul(*b)),
                    Op::SaturatingPlus => Some(a.saturating_add(*b)),
                    Op::SaturatingMinus => Some(a.saturating_sub(*b)),
                    Op::SaturatingTimes => Some(a.saturating_mul(*b)),
                    Op::Remainder => a.checked_rem(*b),
                    Op::Power => {
                        // the built-in power gives 0 for y<0 and 0 for
                        // 0^y; past 62 it stays for the T0603 limit
                        if *b >= 0 && *b <= 62 {
                            if *b > 0 {
                                if *a == 0 {
                                    Some(0)
                                } else {
                                    a.checked_pow(*b as u32)
                                }
                            } else {
                                Some(1)
                            }
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(v) = pick {
                    // only fold if the result kind matches the original
                    if original_kind != Kind::Whole {
                        return false;
                    }
                    e.kind = Kind::Whole;
                    e.e = E::Whole(v);
                    return true;
                }
            }
            // the numeric path: a decimal anywhere promotes the whole side
            // (bin_op's rule); whole/whole keeps its own checked path above
            let ld = matches!(&l.e, E::Dec(_));
            let rd = matches!(&r.e, E::Dec(_));
            if ld || rd {
                let la = match (&l.e, ld) {
                    (E::Whole(a), true) => Some(*a as f64),
                    (E::Dec(a), _) => Some(*a),
                    _ => None,
                };
                let ra = match (&r.e, rd) {
                    (E::Whole(a), true) => Some(*a as f64),
                    (E::Dec(a), _) => Some(*a),
                    _ => None,
                };
                if let (Some(fa), Some(fb)) = (la, ra) {
                    match op {
                        Op::DividedBy => {
                            if fb != 0.0 && original_kind == Kind::Decimal {
                                let v = fa / fb;
                                e.kind = Kind::Decimal;
                                e.e = E::Dec(v);
                                return true;
                            }
                        }
                        Op::Plus | Op::Minus | Op::Time
                            if fb.is_finite() && original_kind == Kind::Decimal =>
                        {
                            let v = match op {
                                Op::Plus => fa + fb,
                                Op::Minus => fa - fb,
                                _ => fa * fb,
                            };
                            if v.is_finite() {
                                e.kind = Kind::Decimal;
                                e.e = E::Dec(v);
                                return true;
                            }
                        }
                        _ => {}
                    }
                }
            }
            false
        }
        E::Neg(inner) => match &inner.e {
            // the built-in minus sends a whole number past the lowest
            // number to big-number land, so that overflow must not fold
            E::Whole(a) if *a != i64::MIN => {
                if original_kind != Kind::Whole {
                    return false;
                }
                let v = -a;
                e.kind = Kind::Whole;
                e.e = E::Whole(v);
                true
            }
            E::Dec(a) => {
                if original_kind != Kind::Decimal {
                    return false;
                }
                let v = -1.0 * *a;
                if v.is_finite() {
                    e.e = E::Dec(v);
                    true
                } else {
                    false
                }
            }
            _ => false,
        },
        E::AndOr(l, r, is_and) => {
            if let (E::Boolean(a), E::Boolean(b)) = (&l.e, &r.e) {
                if original_kind != Kind::Boolean {
                    return false;
                }
                let v = if *is_and { *a && *b } else { *a || *b };
                e.kind = Kind::Boolean;
                e.e = E::Boolean(v);
                true
            } else {
                false
            }
        }
        E::AsWhole(inner) => {
            if let E::Whole(a) = inner.e {
                if original_kind != Kind::Whole {
                    return false;
                }
                e.kind = Kind::Whole;
                e.e = E::Whole(a);
                true
            } else {
                false
            }
        }
        E::AsDecimal(inner) => match &inner.e {
            E::Whole(a) => {
                if original_kind != Kind::Decimal {
                    return false;
                }
                e.kind = Kind::Decimal;
                e.e = E::Dec(*a as f64);
                true
            }
            E::Dec(a) => {
                if original_kind != Kind::Decimal {
                    return false;
                }
                e.kind = Kind::Decimal;
                e.e = E::Dec(*a);
                true
            }
            _ => false,
        },
        _ => false,
    }
}

// =================================================== children of a node

/// Every expression held directly inside `e`. Variants that hold none
/// (literals, words, names, patterns, the pronouns) return an empty list;
/// missing a nested walk there would only skip a fold opportunity, never
/// change a value.
pub(crate) fn children_mut(e: &mut Expr) -> Vec<&mut Expr> {
    match &mut e.e {
        E::Binary { l, r, .. }
        | E::DivWhole(l, r)
        | E::Rem(l, r)
        | E::Pow(l, r)
        | E::AndOr(l, r, ..)
        | E::PairOf(l, r) => {
            vec![l.as_mut(), r.as_mut()]
        }
        E::Neg(i)
        | E::Factorial(i)
        | E::CountIn(i)
        | E::Lower(i)
        | E::AsWhole(i)
        | E::AsDecimal(i)
        | E::AsBig(i)
        | E::AsText(i)
        | E::AsNumber(i)
        | E::AsMaybe(i)
        | E::FirstOf(i)
        | E::SecondOf(i)
        | E::JoinedWith(i, _)
        | E::Upper(i)
        | E::Trimmed(i)
        | E::Normalized(i)
        | E::CopyOf(i)
        | E::Move(i)
        | E::Share(i)
        | E::WeakShare(i)
        | E::FirstFib(i)
        | E::PrimesTo(i)
        | E::LastOf(i)
        | E::IsEmpty(i)
        | E::JsonOf(i) => {
            vec![i.as_mut()]
        }
        // M4-7 (7.7): the time and secret reads walk their one child.
        E::MomentAt { date, .. }
        | E::InZone { base: date, .. }
        | E::TimeShift { base: date, .. }
        | E::RandomItem { list: date }
        | E::Shuffled { list: date }
        | E::HashOf(date)
        | E::SecretOf(date)
        | E::Reveal(date) => {
            vec![date.as_mut()]
        }
        E::DaysBetween { a, b } | E::SecondsBetween { a, b } | E::RandomRange { a, b } => {
            vec![a.as_mut(), b.as_mut()]
        }
        E::Round(i, _) => vec![i.as_mut()],
        E::Call { args, .. } => args.iter_mut().collect(),
        E::ListOf(items) | E::Flat(items) => items.iter_mut().collect(),
        E::MinMax { items, .. } => items.iter_mut().collect(),
        E::RecordOf { parts, .. } | E::EnumOf { parts, .. } => {
            parts.iter_mut().map(|p| &mut p.1).collect()
        }
        E::Combine { list, .. } | E::ApplyEach { list, .. } => vec![list.as_mut()],
        E::Sorted(i, _) => vec![i.as_mut()],
        E::Reverse(i) | E::Unique(i) => vec![i.as_mut()],
        E::Fallback { value, default } => vec![value.as_mut(), default.as_mut()],
        E::PartOf { base, .. } => vec![base.as_mut()],
        E::ItemN { list, n } | E::SafeItemN { list, n } | E::FirstN { list, n } => {
            vec![list.as_mut(), n.as_mut()]
        }
        E::ItemsRange { list, from, to } => {
            vec![list.as_mut(), from.as_mut(), to.as_mut()]
        }
        E::Where { list, cond } => vec![list.as_mut(), cond.as_mut()],
        E::AsDyn { value, .. } => vec![value.as_mut()],
        E::PositionOf { haystack, needle } => {
            vec![haystack.as_mut(), needle.as_mut()]
        }
        E::ValueOf { map, key } => vec![map.as_mut(), key.as_mut()],
        E::Has { coll, item } => vec![coll.as_mut(), item.as_mut()],
        E::Union { a, b }
        | E::Overlap { a, b }
        | E::Difference { a, b }
        | E::Split { text: a, sep: b } => vec![a.as_mut(), b.as_mut()],
        E::Replace { pat, repl, text } => {
            vec![pat.as_mut(), repl.as_mut(), text.as_mut()]
        }
        E::Compare(c) => {
            let mut v = vec![c.l.as_mut()];
            v.extend(c.r.iter_mut().map(|x| x.as_mut()));
            v
        }
        _ => vec![],
    }
}

// ================================================== unreachable code

fn drop_unreachable(prog: &mut Program) -> usize {
    let mut dropped = 0;
    every_list(prog, &mut |list| {
        if let Some(i) = list.iter().position(|st| exits_early(st)) {
            dropped += list.len() - 1 - i;
            list.truncate(i + 1);
        }
    });
    dropped
}

/// The interpreter leaves the body at a give back, Stop, Skip, or Fail;
/// everything after the first of those in one list never runs.
fn exits_early(st: &Stmt) -> bool {
    matches!(
        st,
        Stmt::GiveBack(_) | Stmt::Stop | Stmt::Skip | Stmt::Fail { .. }
    )
}

// ====================================================== unused names

fn drop_unused_names(prog: &mut Program) -> usize {
    // a function captures the fixed top-level names written before it, so
    // a definition a body never reads can still be alive through one
    let mut captured: HashSet<String> = HashSet::new();
    for f in prog.funcs.iter() {
        for c in &f.captures {
            captured.insert(c.clone());
        }
    }
    for imp in prog.impls.iter() {
        for f in &imp.funcs {
            for c in &f.captures {
                captured.insert(c.clone());
            }
        }
    }
    collect_capture_names(&prog.body, &mut captured);
    for f in prog.funcs.iter() {
        if let sem::FnBody::Block(s) = &f.body {
            collect_capture_names(s, &mut captured);
        }
    }
    for imp in prog.impls.iter() {
        collect_capture_names(&imp.body, &mut captured);
        for f in &imp.funcs {
            if let sem::FnBody::Block(s) = &f.body {
                collect_capture_names(s, &mut captured);
            }
        }
    }

    let mut dropped = 0;
    every_list(prog, &mut |list| {
        let mut used: HashSet<String> = HashSet::new();
        for st in list.iter() {
            collect_stmt_reads(st, &mut used);
        }
        list.retain(|st| match st {
            Stmt::Define(d) => {
                let dead =
                    !used.contains(&d.name) && !captured.contains(&d.name) && expr_is_pure(&d.expr);
                if dead {
                    dropped += 1;
                }
                !dead
            }
            _ => true,
        });
    });
    dropped
}

/// Names a body references through its own writing steps (the target
/// collection of an Add/Put/Remove step) or through local functions
/// defined inside it (their captures and their nested steps).
fn collect_capture_names(stmts: &[Stmt], into: &mut HashSet<String>) {
    for st in stmts {
        match st {
            // a fresh value enters the holder below, so the holder stays
            // referenced even if no read ever walks over it
            Stmt::Set { name, .. } => {
                into.insert(name.clone());
            }
            Stmt::Append { list, .. }
            | Stmt::Put { map: list, .. }
            | Stmt::Remove { coll: list, .. }
            | Stmt::RemoveFirst { coll: list } => {
                into.insert(list.clone());
            }
            Stmt::SetPart { path, .. } => {
                if let Some(first) = path.first() {
                    into.insert(first.clone());
                }
            }
            Stmt::DefineLocalFn(f) => {
                for c in &f.captures {
                    into.insert(c.clone());
                }
                if let sem::FnBody::Block(s) = &f.body {
                    collect_capture_names(s, into);
                }
            }
            _ => {}
        }
    }
}

// ====================================================== name reads

/// Every name the statement (or anything nested inside it) reads. The
/// listed collection of an Add/Put/Remove step and the captures of a
/// local function count as references, which keeps the pass conservative.
fn collect_stmt_reads(st: &Stmt, used: &mut HashSet<String>) {
    match st {
        Stmt::Note
        | Stmt::Stop
        | Stmt::Skip
        | Stmt::PassFailureUp
        | Stmt::Share { .. }
        | Stmt::Use { .. }
        | Stmt::Close { .. }
        | Stmt::RemoveFirst { .. }
        | Stmt::DefineEnum { .. } => {}
        Stmt::Define(d) => {
            collect_expr_reads(&d.expr, used);
            if let Some(f) = &d.fallback {
                collect_expr_reads(f, used);
            }
        }
        Stmt::Set { name, expr } => {
            collect_expr_reads(expr, used);
            used.insert(name.clone());
        }
        Stmt::Say { expr, .. } => collect_expr_reads(expr, used),
        Stmt::Ask { fallback, .. } => {
            if let Some(e) = fallback {
                collect_expr_reads(e, used);
            }
        }
        Stmt::If { branches, other } => {
            for (cond, body) in branches {
                collect_expr_reads(cond, used);
                collect_stmts_reads(body, used);
            }
            if let Some(ob) = other {
                collect_stmts_reads(ob, used);
            }
        }
        Stmt::RepeatTimes { count, body } => {
            collect_expr_reads(count, used);
            collect_stmts_reads(body, used);
        }
        Stmt::RepeatForever { body } => collect_stmts_reads(body, used),
        Stmt::RepeatWhile { cond, body } => {
            collect_expr_reads(cond, used);
            collect_stmts_reads(body, used);
        }
        Stmt::ForRange { from, to, body, .. } => {
            collect_expr_reads(from, used);
            collect_expr_reads(to, used);
            collect_stmts_reads(body, used);
        }
        Stmt::ForIn { list, body, .. } => {
            collect_expr_reads(list, used);
            collect_stmts_reads(body, used);
        }
        Stmt::Evaluate { expr, .. } => collect_expr_reads(expr, used),
        Stmt::Append { value, list } => {
            collect_expr_reads(value, used);
            used.insert(list.clone());
        }
        Stmt::Put { map, key, value } => {
            collect_expr_reads(value, used);
            if let Some(k) = key {
                collect_expr_reads(k, used);
            }
            used.insert(map.clone());
        }
        Stmt::Remove { coll, value } => {
            collect_expr_reads(value, used);
            used.insert(coll.clone());
        }
        Stmt::SetPart { path, expr } => {
            collect_expr_reads(expr, used);
            if let Some(first) = path.first() {
                used.insert(first.clone());
            }
        }
        Stmt::LookAt { value, whens } => {
            collect_expr_reads(value, used);
            for w in whens {
                collect_stmts_reads(&w.body, used);
            }
        }
        Stmt::Try {
            sentence,
            success,
            failure,
        } => {
            collect_stmt_reads(sentence, used);
            collect_stmts_reads(success, used);
            for (_, arms) in failure {
                collect_stmts_reads(arms, used);
            }
        }
        Stmt::Fail { message } => collect_expr_reads(message, used),
        Stmt::Test { body, .. } => collect_stmts_reads(body, used),
        Stmt::Check { cond, body, .. } => {
            if let Some(c) = cond {
                collect_expr_reads(c, used);
            }
            collect_stmts_reads(body, used);
        }
        Stmt::Pretend { value, .. } => collect_expr_reads(value, used),
        Stmt::GiveBack(e) => {
            if let Some(e) = e {
                collect_expr_reads(e, used);
            }
        }
        Stmt::HandBack(e) => collect_expr_reads(e, used),
        Stmt::DefineLocalFn(f) => {
            for c in &f.captures {
                used.insert(c.clone());
            }
            match &f.body {
                sem::FnBody::Block(s) => collect_stmts_reads(s, used),
                sem::FnBody::Expr(e) => collect_expr_reads(e, used),
            }
        }
        // M4 (Appendix K): a task body's reads count too (conservative);
        // wait/sleep/stop read nothing.
        Stmt::StartTask { body, .. } | Stmt::DoTogether { body } => collect_stmts_reads(body, used),
        Stmt::WaitFor { .. } | Stmt::StopTask { .. } | Stmt::SleepFor { .. } => {}
        // M4 (Appendix K): Send/AtomicAdd read their value; Receive reads
        // only the channel name it receives from.
        Stmt::Send { value, .. } | Stmt::AtomicAdd { value, .. } => collect_expr_reads(value, used),
        Stmt::Receive { name } => {
            used.insert(name.clone());
        }
        // M4-4 (Appendix K 7.3/7.4): a stream loop reads its channel and
        // its body; timer bodies read; a spread reads its items and its
        // body; Use N workers. reads nothing.
        Stmt::AfterTimer { body, .. } | Stmt::EveryTimer { body, .. } => {
            collect_stmts_reads(body, used)
        }
        Stmt::StreamLoop { channel, body, .. } => {
            used.insert(channel.clone());
            collect_stmts_reads(body, used)
        }
        Stmt::Spread { items, body } => {
            collect_expr_reads(items, used);
            collect_stmts_reads(body, used)
        }
        Stmt::UseWorkers { .. } => {}
        // M4-7 (7.7): Use seed reads nothing.
        Stmt::UseSeed { .. } => {}
        // M4-5 (Appendix K 7.5): the write/append/replace value reads;
        // the for-each-line / when-file-changes bodies read; the other
        // file sentences hold only literal path words (a temporary file
        // name is DEFINED here, never read as one)
        Stmt::WriteFile { value, .. }
        | Stmt::AppendFile { value, .. }
        | Stmt::ReplaceFile { value, .. } => collect_expr_reads(value, used),
        Stmt::ForEachLine { body, .. } | Stmt::WhenFileChanges { body, .. } => {
            collect_stmts_reads(body, used)
        }
        Stmt::ReadFile { .. }
        | Stmt::ReadBytes { .. }
        | Stmt::ListFolder { .. }
        | Stmt::MakeFolder { .. }
        | Stmt::RemovePath { .. }
        | Stmt::MovePath { .. }
        | Stmt::DuplicatePath { .. }
        | Stmt::MakeTempFile { .. }
        | Stmt::ZipOp { .. }
        | Stmt::ReadFormat { .. } => {}
        Stmt::SaveFormat { value, .. } | Stmt::ReadFormatText { value, .. } => {
            collect_expr_reads(value, used)
        }
        // M4-8 (7.10/7.11): the Run arguments read; the signal and input
        // loop bodies read; Exit carries only a literal code.
        Stmt::RunProc { args, .. } => {
            for a in args {
                collect_expr_reads(a, used);
            }
        }
        Stmt::Exit { .. } => {}
        // M4-9 (7.12): the Log text reads as in Say; Use log level reads
        // nothing
        Stmt::Log { expr, .. } => collect_expr_reads(expr, used),
        Stmt::LogLevel { .. } => {}
        // M4-10 (7.8): the fetch/post/send values read; the handler
        // bodies read (they run in the enclosing context)
        Stmt::Fetch {
            data,
            headers,
            query,
            ..
        } => {
            if let Some(d) = data {
                collect_expr_reads(d, used);
            }
            for (_, e) in headers.iter().chain(query.iter()) {
                collect_expr_reads(e, used);
            }
        }
        Stmt::PostTo { data, .. } => collect_expr_reads(data, used),
        Stmt::WsSend { value } => collect_expr_reads(value, used),
        Stmt::Serve { body, .. } | Stmt::WhenSomeone { body, .. } | Stmt::WhenLive { body, .. } => {
            collect_stmts_reads(body, used)
        }
        Stmt::Respond { kind, .. } => match kind {
            sem::RespondKind::Text(e)
            | sem::RespondKind::Json(e)
            | sem::RespondKind::Literally(e) => collect_expr_reads(e, used),
            sem::RespondKind::Status(_, Some(e)) => collect_expr_reads(e, used),
            sem::RespondKind::Status(_, None) | sem::RespondKind::Template(_) => {}
        },
        Stmt::PageDecl { .. } | Stmt::WsRecv { .. } => {}
        Stmt::Careful { body } => collect_stmts_reads(body, used),
        Stmt::WhenSignal { body, .. } | Stmt::ForEachInput { body, .. } => {
            collect_stmts_reads(body, used)
        }
    }
}

fn collect_stmts_reads(stmts: &[Stmt], used: &mut HashSet<String>) {
    for st in stmts {
        collect_stmt_reads(st, used);
    }
}

fn collect_expr_reads(e: &Expr, used: &mut HashSet<String>) {
    if let E::Name(n) = &e.e {
        used.insert(n.clone());
    }
    for child in probe_children(e) {
        collect_expr_reads(child, used);
    }
}

/// Shared-borrow mirror of `children_mut` for read-only walks.
fn probe_children(e: &Expr) -> Vec<&Expr> {
    match &e.e {
        E::Binary { l, r, .. }
        | E::DivWhole(l, r)
        | E::Rem(l, r)
        | E::Pow(l, r)
        | E::AndOr(l, r, ..)
        | E::PairOf(l, r) => {
            vec![l.as_ref(), r.as_ref()]
        }
        E::Neg(i)
        | E::Factorial(i)
        | E::CountIn(i)
        | E::Lower(i)
        | E::AsWhole(i)
        | E::AsDecimal(i)
        | E::AsBig(i)
        | E::AsText(i)
        | E::AsNumber(i)
        | E::AsMaybe(i)
        | E::FirstOf(i)
        | E::SecondOf(i)
        | E::JoinedWith(i, _)
        | E::Upper(i)
        | E::Trimmed(i)
        | E::Normalized(i)
        | E::CopyOf(i)
        | E::Move(i)
        | E::Share(i)
        | E::WeakShare(i)
        | E::FirstFib(i)
        | E::PrimesTo(i)
        | E::LastOf(i)
        | E::IsEmpty(i)
        | E::JsonOf(i) => {
            vec![i.as_ref()]
        }
        // M4-7 (7.7): the time and secret reads walk their one child.
        E::MomentAt { date, .. }
        | E::InZone { base: date, .. }
        | E::TimeShift { base: date, .. }
        | E::RandomItem { list: date }
        | E::Shuffled { list: date }
        | E::HashOf(date)
        | E::SecretOf(date)
        | E::Reveal(date) => {
            vec![date.as_ref()]
        }
        E::DaysBetween { a, b } | E::SecondsBetween { a, b } | E::RandomRange { a, b } => {
            vec![a.as_ref(), b.as_ref()]
        }
        E::Round(i, _) => vec![i.as_ref()],
        E::Call { args, .. } => args.iter().collect(),
        E::ListOf(items) | E::Flat(items) => items.iter().collect(),
        E::MinMax { items, .. } => items.iter().collect(),
        E::RecordOf { parts, .. } | E::EnumOf { parts, .. } => parts.iter().map(|p| &p.1).collect(),
        E::Combine { list, .. } | E::ApplyEach { list, .. } => vec![list.as_ref()],
        E::Sorted(i, _) => vec![i.as_ref()],
        E::Reverse(i) | E::Unique(i) => vec![i.as_ref()],
        E::Fallback { value, default } => vec![value.as_ref(), default.as_ref()],
        E::PartOf { base, .. } => vec![base.as_ref()],
        E::ItemN { list, n } | E::SafeItemN { list, n } | E::FirstN { list, n } => {
            vec![list.as_ref(), n.as_ref()]
        }
        E::ItemsRange { list, from, to } => {
            vec![list.as_ref(), from.as_ref(), to.as_ref()]
        }
        E::Where { list, cond } => vec![list.as_ref(), cond.as_ref()],
        E::AsDyn { value, .. } => vec![value.as_ref()],
        E::PositionOf { haystack, needle } => {
            vec![haystack.as_ref(), needle.as_ref()]
        }
        E::ValueOf { map, key } => vec![map.as_ref(), key.as_ref()],
        E::Has { coll, item } => vec![coll.as_ref(), item.as_ref()],
        E::Union { a, b }
        | E::Overlap { a, b }
        | E::Difference { a, b }
        | E::Split { text: a, sep: b } => vec![a.as_ref(), b.as_ref()],
        E::Replace { pat, repl, text } => {
            vec![pat.as_ref(), repl.as_ref(), text.as_ref()]
        }
        E::Compare(c) => {
            let mut v = vec![c.l.as_ref()];
            v.extend(c.r.iter().map(|x| x.as_ref()));
            v
        }
        _ => vec![],
    }
}

/// A right-hand side that cannot possibly print, ask, fail, or hand back:
/// only then may an unread definition disappear without a trace.
fn expr_is_pure(e: &Expr) -> bool {
    match &e.e {
        E::Whole(_) | E::Dec(_) | E::Boolean(_) | E::Missing | E::Word(_) | E::Name(_) => true,
        E::Binary { l, r, .. }
        | E::DivWhole(l, r)
        | E::Rem(l, r)
        | E::Pow(l, r)
        | E::AndOr(l, r, ..)
        | E::PairOf(l, r) => expr_is_pure(l) && expr_is_pure(r),
        E::Neg(inner)
        | E::Round(inner, _)
        | E::AsWhole(inner)
        | E::AsDecimal(inner)
        | E::AsBig(inner)
        | E::CountIn(inner) => expr_is_pure(inner),
        E::ListOf(items) | E::Flat(items) | E::MinMax { items, .. } => {
            items.iter().all(expr_is_pure)
        }
        E::Compare(c) => expr_is_pure(&c.l) && c.r.iter().all(|x| expr_is_pure(x)),
        _ => false,
    }
}

// ========================================================== inlining

/// One inlinable function: the callee name, its input names in order, the
/// body expression, and how often each input appears in the body.
struct Cand {
    name: String,
    params: Vec<String>,
    body: Expr,
    counts: HashMap<String, usize>,
}

fn inline_calls(prog: &mut Program) -> usize {
    // `Pretend f gives V` replaces a whole function's result for the
    // statements that follow; inlining would bypass the pretend stand-in
    if program_has_pretend(prog) {
        return 0;
    }
    let mut cands: Vec<Cand> = Vec::new();
    collect_candidates(prog, &mut cands);
    if cands.is_empty() {
        return 0;
    }
    // An interface function's call (`speak rex`) is dispatched at run time
    // on the value's kind (ch.23, M3-S18). Impl blocks of different kinds
    // define functions with the SAME name, so a name-keyed inline map would
    // resolve every dynamic dispatch to whichever impl was collected last
    // and break byte-exactness. Those names belong to the dispatcher.
    let dyn_calls: std::collections::HashSet<String> =
        prog.interfaces.iter().map(|i| i.fn_name.clone()).collect();
    let mut subs: HashMap<String, usize> = HashMap::new();
    for (i, c) in cands.iter().enumerate() {
        if dyn_calls.contains(&c.name) {
            continue;
        }
        subs.insert(c.name.clone(), i);
    }

    let mut changes = 0;
    let mut visit = |e: &mut Expr| {
        inline_root(e, &subs, &cands, &mut changes);
    };

    // the top-level body, function bodies, and implementation bodies; test
    // bodies are left alone (tests run in their own command)
    for st in prog.body.iter_mut() {
        map_stmt_exprs(st, &mut visit);
    }
    for f in prog.funcs.iter_mut() {
        match &mut f.body {
            sem::FnBody::Expr(e) => visit(e),
            sem::FnBody::Block(s) => {
                for st in s.iter_mut() {
                    map_stmt_exprs(st, &mut visit);
                }
            }
        }
    }
    for imp in prog.impls.iter_mut() {
        for st in imp.body.iter_mut() {
            map_stmt_exprs(st, &mut visit);
        }
        for f in imp.funcs.iter_mut() {
            match &mut f.body {
                sem::FnBody::Expr(e) => visit(e),
                sem::FnBody::Block(s) => {
                    for st in s.iter_mut() {
                        map_stmt_exprs(st, &mut visit);
                    }
                }
            }
        }
    }
    changes
}

/// Bottom-up call-site replacement inside one expression.
fn inline_root(e: &mut Expr, subs: &HashMap<String, usize>, cands: &[Cand], changes: &mut usize) {
    for child in children_mut(e) {
        inline_root(child, subs, cands, changes);
    }
    let mut repl: Option<Expr> = None;
    if let E::Call { name, args } = &e.e {
        if let Some(ci) = subs.get(name) {
            let cand = &cands[*ci];
            if should_inline(cand, args) {
                repl = Some(substitute(cand, args));
            }
        }
    }
    if let Some(r) = repl {
        *e = r;
        *changes += 1;
    }
}

fn should_inline(cand: &Cand, args: &[Expr]) -> bool {
    if args.len() != cand.params.len() {
        return false;
    }
    for (pi, p) in cand.params.iter().enumerate() {
        let n = cand.counts.get(p).copied().unwrap_or(0);
        let a = &args[pi];
        if n == 0 {
            // the call evaluates every argument, even an unread one, so an
            // inlined unread argument must be side-effect free
            if !expr_is_pure(a) {
                return false;
            }
        } else if n == 1 {
            // evaluated exactly once, like the call did: any argument fits
        } else {
            // repeated use would also repeat the argument's work
            if !matches!(
                a.e,
                E::Whole(_) | E::Dec(_) | E::Boolean(_) | E::Word(_) | E::Missing
            ) {
                return false;
            }
        }
        // whole- or unknown-kind arguments only: the substituted
        // expression then scans exactly like the call it replaces
        if !matches!(a.kind, Kind::Whole | Kind::Unknown) {
            return false;
        }
    }
    true
}

/// Replace the callee's input names with the call's arguments, in place,
/// children first. Parameters appear only as leaf names in the body, so
/// a replaced input is never substituted twice.
fn substitute(cand: &Cand, args: &[Expr]) -> Expr {
    let mut out = cand.body.clone();
    subst_into(&mut out, &cand.params, args);
    out
}

fn subst_into(e: &mut Expr, params: &[String], args: &[Expr]) {
    if let E::Name(n) = &e.e {
        if let Some(i) = params.iter().position(|p| p == n) {
            *e = args[i].clone();
            return;
        }
    }
    for child in children_mut(e) {
        subst_into(child, params, args);
    }
}

/// Inline candidates from the program's functions: a single give back (or
/// a one-line body) with no calls or pronouns, body names limited to its
/// own inputs, no contracts, no defaulting last input, no generator.
fn collect_candidates(prog: &Program, out: &mut Vec<Cand>) {
    fn probe(f: &sem::FuncDef, out: &mut Vec<Cand>) {
        // local functions bind by name inside a scope; leave them alone
        if f.is_local || f.is_generator || f.can_fail {
            return;
        }
        if !f.requires.is_empty() || !f.ensures.is_empty() || f.default_last.is_some() {
            return;
        }
        let body: &Expr = match &f.body {
            sem::FnBody::Expr(e) => e,
            sem::FnBody::Block(s) => {
                if s.len() != 1 {
                    return;
                }
                match &s[0] {
                    Stmt::GiveBack(Some(e)) => e,
                    _ => return,
                }
            }
        };
        if expr_has_call_or_pronoun(body) {
            return;
        }
        let params: Vec<String> = f.inputs.iter().map(|(n, _)| n.clone()).collect();
        let mut counts: HashMap<String, usize> = HashMap::new();
        count_names(body, &mut counts);
        // the body must mention no name beyond its own inputs: any other
        // name resolves where the function was written, and inlining would
        // re-resolve it at the call site instead
        for n in counts.keys() {
            if !params.contains(n) {
                return;
            }
        }
        out.push(Cand {
            name: f.name.clone(),
            params,
            body: body.clone(),
            counts,
        });
    }
    for f in &prog.funcs {
        probe(f, out);
    }
    for imp in &prog.impls {
        for f in &imp.funcs {
            probe(f, out);
        }
    }
}

fn count_names(body: &Expr, counts: &mut HashMap<String, usize>) {
    if let E::Name(n) = &body.e {
        *counts.entry(n.clone()).or_insert(0) += 1;
    }
    for child in probe_children(body) {
        count_names(child, counts);
    }
}

fn expr_has_call_or_pronoun(e: &Expr) -> bool {
    match &e.e {
        E::Call { .. } | E::It | E::Them => true,
        _ => probe_children(e)
            .iter()
            .any(|c| expr_has_call_or_pronoun(c)),
    }
}

/// Whether any Pretend stands in for a function outside the test blocks
/// (those are not touched by this pass).
fn program_has_pretend(prog: &Program) -> bool {
    fn stmts_have(lists: &[&[Stmt]]) -> bool {
        for list in lists {
            if has_pretend_in(list) {
                return true;
            }
        }
        false
    }
    let mut fn_lists: Vec<&[Stmt]> = Vec::new();
    for f in &prog.funcs {
        if let sem::FnBody::Block(s) = &f.body {
            fn_lists.push(s);
        }
    }
    for imp in &prog.impls {
        fn_lists.push(&imp.body);
        for f in &imp.funcs {
            if let sem::FnBody::Block(s) = &f.body {
                fn_lists.push(s);
            }
        }
    }
    stmts_have(&[&prog.body]) || stmts_have(&fn_lists)
}

fn has_pretend_in(stmts: &[Stmt]) -> bool {
    for st in stmts {
        match st {
            Stmt::Pretend { .. } => return true,
            Stmt::If { branches, other } => {
                if branches.iter().any(|(_, b)| has_pretend_in(b)) {
                    return true;
                }
                if other.iter().any(|ob| has_pretend_in(ob)) {
                    return true;
                }
            }
            Stmt::RepeatTimes { body, .. }
            | Stmt::RepeatForever { body }
            | Stmt::RepeatWhile { body, .. }
            | Stmt::ForRange { body, .. }
            | Stmt::ForIn { body, .. }
            | Stmt::Test { body, .. }
            | Stmt::Check { body, .. } => {
                if has_pretend_in(body) {
                    return true;
                }
            }
            Stmt::LookAt { whens, .. } => {
                if whens.iter().any(|w| has_pretend_in(&w.body)) {
                    return true;
                }
            }
            Stmt::Try {
                sentence,
                success,
                failure,
            } => {
                if has_pretend_in(std::slice::from_ref(sentence)) {
                    return true;
                }
                if has_pretend_in(success) {
                    return true;
                }
                if failure.iter().any(|(_, arms)| has_pretend_in(arms)) {
                    return true;
                }
            }
            Stmt::DefineLocalFn(f) => {
                if let sem::FnBody::Block(s) = &f.body {
                    if has_pretend_in(s) {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

// ===================================================== tail calls

/// Count `give back <name> ...` self-calls. Report only: the running
/// depth limit (T0607) must stay observable, so no loop conversion.
fn mark_tail_calls(prog: &mut Program) -> usize {
    let mut tails = 0;
    for f in prog.funcs.iter() {
        if let sem::FnBody::Block(s) = &f.body {
            tails += count_tail_in(s, &f.name);
        }
    }
    for imp in prog.impls.iter() {
        for f in &imp.funcs {
            if let sem::FnBody::Block(s) = &f.body {
                tails += count_tail_in(s, &f.name);
            }
        }
    }
    tails
}

fn count_tail_in(stmts: &[Stmt], name: &str) -> usize {
    let mut n = 0;
    for st in stmts {
        if let Stmt::GiveBack(Some(e)) = st {
            if let E::Call { name: called, .. } = &e.e {
                if called == name {
                    n += 1;
                }
            }
        }
        n += count_tail_nested(st, name);
    }
    n
}

fn count_tail_nested(st: &Stmt, name: &str) -> usize {
    let mut total = 0;
    fn visit(list: &[Stmt], name: &str, total: &mut usize) {
        *total += count_tail_in(list, name);
    }
    match st {
        Stmt::If { branches, other } => {
            for (_, body) in branches {
                visit(body, name, &mut total);
            }
            if let Some(ob) = other {
                visit(ob, name, &mut total);
            }
        }
        Stmt::RepeatTimes { body, .. }
        | Stmt::RepeatForever { body }
        | Stmt::RepeatWhile { body, .. }
        | Stmt::ForRange { body, .. }
        | Stmt::ForIn { body, .. }
        | Stmt::Test { body, .. }
        | Stmt::Check { body, .. } => visit(body, name, &mut total),
        Stmt::LookAt { whens, .. } => {
            for w in whens {
                visit(&w.body, name, &mut total);
            }
        }
        Stmt::Try {
            sentence,
            success,
            failure,
        } => {
            if let Stmt::GiveBack(Some(e)) = sentence.as_ref() {
                if let E::Call { name: called, .. } = &e.e {
                    if called == name {
                        total += 1;
                    }
                }
            }
            visit(success, name, &mut total);
            for (_, arms) in failure {
                visit(arms, name, &mut total);
            }
        }
        Stmt::DefineLocalFn(f) => {
            if let sem::FnBody::Block(s) = &f.body {
                total += count_tail_in(s, name);
            }
        }
        _ => {}
    }
    total
}

// =================================================== bounds-check elimination

/// Scan for `ItemN`/`SafeItemN` with constant indices where the index is
/// provably within the list's bounds. The scalar codegen does not lower
/// list operations in M3 (they run through the evaluator), so this pass
/// currently finds nothing to eliminate — but the analysis is in place
/// for when list lowering lands.
fn eliminate_bounds_checks(prog: &mut Program) -> usize {
    let mut eliminated = 0;
    every_list(prog, &mut |list| {
        for st in list.iter_mut() {
            eliminated += eliminate_bounds_in_stmt(st);
        }
    });
    for f in &mut prog.funcs {
        if let sem::FnBody::Expr(e) = &mut f.body {
            eliminated += eliminate_bounds_in_expr(e);
        }
    }
    for imp in &mut prog.impls {
        for f in &mut imp.funcs {
            if let sem::FnBody::Expr(e) = &mut f.body {
                eliminated += eliminate_bounds_in_expr(e);
            }
        }
    }
    eliminated
}

fn eliminate_bounds_in_stmt(st: &mut Stmt) -> usize {
    let mut n = 0;
    map_stmt_exprs(st, &mut |e| {
        n += eliminate_bounds_in_expr(e);
    });
    n
}

fn eliminate_bounds_in_expr(e: &mut Expr) -> usize {
    let mut n = 0;
    for child in children_mut(e) {
        n += eliminate_bounds_in_expr(child);
    }
    match &e.e {
        E::ItemN { .. } | E::SafeItemN { .. } => {
            // A constant item of a literal list, proven in bounds, needs no
            // index check at run time: the access becomes the item itself
            // (ch.66: bounds-check elimination). The proof is sound only
            // when every part of the literal is a constant that cannot
            // fail — evaluating exactly one part must behave like building
            // the whole list and indexing it. Lists that are values at run
            // time (a list that lives in a name) stay checked.
            if let Some(item) = prove_literal_index(&e.e) {
                *e = item;
                n += 1;
            }
        }
        _ => {}
    }
    n
}

/// Prove `item k of (list of parts...)` in bounds at compile time: `k` is a
/// constant in 1..=parts.len() and every part cannot fail, so the whole
/// checked access is replaced by the part itself.
fn prove_literal_index(e: &E) -> Option<Expr> {
    let (list, n) = match e {
        E::ItemN { list, n } | E::SafeItemN { list, n } => (list, n),
        _ => return None,
    };
    let items = match &list.e {
        E::ListOf(items) => items,
        _ => return None,
    };
    let k = match &n.e {
        E::Whole(k) => *k,
        _ => return None,
    };
    // lists are 1-indexed (item 1 of ...)
    if k < 1 || k as usize > items.len() {
        return None;
    }
    let item = &items[(k - 1) as usize];
    if !expr_cannot_fail(item) {
        return None;
    }
    Some(item.clone())
}

/// Conservative "cannot fail": constant literals and literal lists/pairs of
/// those. Arithmetic is excluded even when pure — a whole number run can
/// always overflow, and the checked item would have surfaced that failure
/// before the index check the pass removes.
fn expr_cannot_fail(e: &Expr) -> bool {
    match &e.e {
        E::Whole(_) | E::Dec(_) | E::Boolean(_) | E::Missing => true,
        E::ListOf(items) => items.iter().all(expr_cannot_fail),
        E::PairOf(l, r) => expr_cannot_fail(l) && expr_cannot_fail(r),
        _ => false,
    }
}

// ====================================================== devirtualization

/// Devirtualize (ch.23, M3): when an interface call's receiver kind is
/// known statically, replace the run-time dispatch with a direct call.
/// The impl's function is copied into `prog.funcs` under the mangled name
/// `fn@kind` (the parser never puts `@` in a word, so the name cannot
/// collide with a written function) and each matching call site is
/// rewritten to call it. The copied body runs exactly as the dispatch did
/// (same receiver binding, no extra captured names), so the run outcome is
/// byte-identical. No rewrite happens for unknown kinds (`as any` values
/// that came from a list, generic inputs), when the impl arity does not
/// match the call, for generators or defaulting inputs (their dispatch
/// paths answer differently), or when a test Pretends the same name.
fn devirtualize(prog: &mut Program) -> usize {
    // A Pretend override (ch.38) intercepts a call by name; do not
    // devirtualize a name any Pretend can answer.
    let mut pretended: HashSet<String> = HashSet::new();
    every_list(prog, &mut |list| collect_pretends(list, &mut pretended));

    // (interface fn name, kind) -> mangled direct-call name
    let mut direct: HashMap<(String, String), String> = HashMap::new();
    for iface in &prog.interfaces {
        for imp in prog.impls.iter() {
            if imp.meaning.is_some() || imp.verb != iface.verb {
                continue;
            }
            let Some(f) = imp.funcs.iter().find(|f| f.name == iface.fn_name) else {
                continue;
            };
            if f.is_generator || f.default_last.is_some() || f.inputs.len() < 1 {
                continue;
            }
            let mangled = format!("{}@{}", iface.fn_name, imp.kind_name);
            if direct.contains_key(&(iface.fn_name.clone(), imp.kind_name.clone())) {
                continue;
            }
            let mut mf = f.clone();
            mf.name = mangled.clone();
            mf.captures = Vec::new(); // the dispatch binds no captured names
            prog.funcs.push(mf);
            direct.insert((iface.fn_name.clone(), imp.kind_name.clone()), mangled);
        }
    }
    let iface_names: HashSet<String> = prog.interfaces.iter().map(|i| i.fn_name.clone()).collect();

    let mut devirt = 0;
    every_list(prog, &mut |list| {
        for st in list.iter_mut() {
            devirt += devirt_in_stmt(st, &direct, &iface_names, &pretended);
        }
    });
    for f in &mut prog.funcs {
        if let sem::FnBody::Expr(e) = &mut f.body {
            devirt += devirt_in_expr(e, &direct, &iface_names, &pretended);
        }
    }
    for imp in &mut prog.impls {
        for f in &mut imp.funcs {
            if let sem::FnBody::Expr(e) = &mut f.body {
                devirt += devirt_in_expr(e, &direct, &iface_names, &pretended);
            }
        }
    }
    devirt
}

/// The names every `Pretend f gives V.` answers (ch.38), including inside
/// nested bodies (If branches, loops, each-of, Try, tests).
fn collect_pretends(stmts: &[Stmt], out: &mut HashSet<String>) {
    for st in stmts {
        match st {
            Stmt::Pretend { name, .. } => {
                out.insert(name.clone());
            }
            Stmt::If { branches, other } => {
                for (_, b) in branches {
                    collect_pretends(b, out);
                }
                if let Some(o) = other {
                    collect_pretends(o, out);
                }
            }
            Stmt::RepeatTimes { body, .. }
            | Stmt::RepeatForever { body }
            | Stmt::RepeatWhile { body, .. }
            | Stmt::ForRange { body, .. }
            | Stmt::ForIn { body, .. }
            | Stmt::Test { body, .. }
            | Stmt::Check { body, .. } => collect_pretends(body, out),
            Stmt::Try {
                sentence,
                success,
                failure,
            } => {
                collect_pretends(std::slice::from_ref(sentence.as_ref()), out);
                collect_pretends(success, out);
                for (_, b) in failure {
                    collect_pretends(b, out);
                }
            }
            Stmt::LookAt { whens, .. } => {
                for w in whens {
                    collect_pretends(&w.body, out);
                }
            }
            _ => {}
        }
    }
}

fn devirt_in_stmt(
    st: &mut Stmt,
    direct: &HashMap<(String, String), String>,
    iface_names: &HashSet<String>,
    pretended: &HashSet<String>,
) -> usize {
    let mut n = 0;
    map_stmt_exprs(st, &mut |e| {
        n += devirt_in_expr(e, direct, iface_names, pretended);
    });
    n
}

/// The record kind of an interface-call receiver, when the compiler knows
/// it statically: a record literal (its type name is in the node), or a
/// name whose kind resolved to a record (sem tracks declared kinds), or
/// the value under an `as any` that wraps such an expression.
fn devirt_receiver_kind(e: &sem::Expr) -> Option<String> {
    match &e.e {
        E::RecordOf { type_name, .. } => Some(type_name.clone()),
        E::AsDyn { value, .. } => match &value.e {
            E::RecordOf { type_name, .. } => Some(type_name.clone()),
            E::Name(_) => match &value.kind {
                Kind::Record(t, _) => Some(t.clone()),
                _ => None,
            },
            _ => None,
        },
        E::Name(_) => match &e.kind {
            Kind::Record(t, _) => Some(t.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn devirt_in_expr(
    e: &mut sem::Expr,
    direct: &HashMap<(String, String), String>,
    iface_names: &HashSet<String>,
    pretended: &HashSet<String>,
) -> usize {
    let mut n = 0;
    for child in children_mut(e) {
        n += devirt_in_expr(child, direct, iface_names, pretended);
    }
    if let E::Call { name, args } = &mut e.e {
        if args.len() >= 1 && iface_names.contains(name) && !pretended.contains(name) {
            let known = devirt_receiver_kind(&args[0]);
            if let Some(kind) = known {
                if let Some(mangled) = direct.get(&(name.clone(), kind)) {
                    name.clone_from(mangled);
                    n += 1;
                }
            }
        }
    }
    n
}
