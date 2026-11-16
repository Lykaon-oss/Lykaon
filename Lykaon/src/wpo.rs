//! Whole-program optimization (M3c, ROADMAP): passes that look at the
//! COMPLETE program tree. Everything a package's Use sentence pulled in
//! already sits in this one tree (lib.rs flattens Use at compile time), so
//! these passes see across every package by construction.
//!
//! Pass 1: dead-function removal. A function that no statement and no
//! other reachable function can call can never run - it is removed from
//! the tree. The rules are deliberately conservative (below under
//! "dead functions").
//!
//! Pass 2 (M3c-2): block-body inlining. A function whose body is a run of
//! plain local `Set` statements ending in one `Give back <expr>` is
//! substituted at its call sites as those Sets (with locals renamed to
//! unnameable synthetic names) plus the final expression. The rules are
//! deliberately conservative (below under "block-body inlining").
//!   * roots: the top-level body, every Test body (`lykaon test` still
//!     runs on the same tree), every interface call name,
//!   * edges: Call, a function reference (Combine with X, Apply each),
//!     and any other expression that names a function,
//!   * never removed: functions marked with Share (a package's public
//!     shape) - callers from outside this exact compile do not appear in
//!     the tree,
//!   * implementation blocks stay whole: the dyn dispatch goes by VALUE
//!     kind at run time, and one kind could yet carry the interface
//!     default. Dead-fn removal only thins `prog.funcs`.
//!
//! Every edge rule errs toward keeping: what stays can only be dead code,
//! what must never be removed is removed-never.

use crate::prover::children;
use crate::sem::{self, E, Expr, FnBody, Program, Stmt};
use std::collections::{HashMap, HashSet};

// ------------------------------------------------------------------ reads

/// Read-only visit of every expression a statement holds (the immutable
/// sibling of optimizer::map_stmt_exprs - same variants, only reads). The
/// built program's runtime uses it for its stdin-reading decision.
pub fn read_stmt_exprs(st: &Stmt, f: &mut dyn FnMut(&Expr)) {
    fn go_list(list: &[Stmt], f: &mut dyn FnMut(&Expr)) {
        for st in list.iter() {
            read_stmt_exprs(st, f);
        }
    }
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
            f(&d.expr);
            if let Some(fb) = &d.fallback {
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
            for (cond, body) in branches.iter() {
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
            for w in whens.iter() {
                go_list(&w.body, f);
            }
        }
        Stmt::Try {
            sentence,
            success,
            failure,
        } => {
            read_stmt_exprs(sentence, f);
            go_list(success, f);
            for (_, arms) in failure.iter() {
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
        Stmt::DefineLocalFn(fbody) => match &fbody.body {
            sem::FnBody::Block(s) => go_list(s, f),
            sem::FnBody::Expr(e) => f(e),
        },
        // M4 (Appendix K): a task body's expressions count as reads too;
        // wait/sleep/stop hold none.
        Stmt::StartTask { body, .. } | Stmt::DoTogether { body } => go_list(body, f),
        Stmt::WaitFor { .. } | Stmt::StopTask { .. } | Stmt::SleepFor { .. } => {}
        // M4 (Appendix K): Send/AtomicAdd hold the value expression;
        // Receive holds only the channel name
        Stmt::Send { value, .. } | Stmt::AtomicAdd { value, .. } => f(value),
        Stmt::Receive { .. } => {}
        // M4-4 (Appendix K 7.3/7.4): timer/stream/spread bodies read;
        // the spread items value is an expression of the caller.
        Stmt::AfterTimer { body, .. }
        | Stmt::EveryTimer { body, .. }
        | Stmt::StreamLoop { body, .. } => go_list(body, f),
        Stmt::Spread { items, body } => {
            f(items);
            go_list(body, f)
        }
        Stmt::UseWorkers { .. } => {}
        // M4-7 (7.7): Use seed carries no expression.
        Stmt::UseSeed { .. } => {}
        // M4-8 (7.10/7.11): the Run arguments read; the signal and input
        // loop bodies read; Exit carries no expression.
        Stmt::RunProc { args, .. } => {
            for a in args {
                f(a);
            }
        }
        Stmt::Exit { .. } => {}
        // M4-9 (7.12): the Log text is read as in Say; Use log level
        // carries no expression.
        Stmt::Log { expr, .. } => f(expr),
        Stmt::LogLevel { .. } => {}
        // M4-10 (7.8): the fetch/post/send values read; the server
        // bodies read (they run inline in the enclosing context)
        Stmt::Fetch {
            data,
            headers,
            query,
            ..
        } => {
            if let Some(d) = data {
                f(d);
            }
            for (_, e) in headers.iter().chain(query.iter()) {
                f(e);
            }
        }
        Stmt::PostTo { data, .. } => f(data),
        Stmt::WsSend { value } => f(value),
        Stmt::Serve { body, .. } | Stmt::WhenSomeone { body, .. } | Stmt::WhenLive { body, .. } => {
            go_list(body, f)
        }
        Stmt::Respond { kind, .. } => match kind {
            sem::RespondKind::Text(e)
            | sem::RespondKind::Json(e)
            | sem::RespondKind::Literally(e) => f(e),
            sem::RespondKind::Status(_, Some(e)) => f(e),
            sem::RespondKind::Status(_, None) | sem::RespondKind::Template(_) => {}
        },
        Stmt::PageDecl { .. } | Stmt::WsRecv { .. } => {}
        Stmt::Careful { body } => go_list(body, f),
        Stmt::WhenSignal { body, .. } | Stmt::ForEachInput { body, .. } => go_list(body, f),
        // M4-5 (Appendix K 7.5): the write/append/replace value reads;
        // the for-each-line / when-file-changes bodies read; the other
        // file sentences hold no expressions.
        Stmt::WriteFile { value, .. }
        | Stmt::AppendFile { value, .. }
        | Stmt::ReplaceFile { value, .. }
        | Stmt::SaveFormat { value, .. }
        | Stmt::ReadFormatText { value, .. } => f(value),
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
        Stmt::ForEachLine { body, .. } | Stmt::WhenFileChanges { body, .. } => go_list(body, f),
    }
}

/// Recursive read of an expression subtree (top node plus descendants).
pub(crate) fn read_expr_deep(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    for c in children(e) {
        read_expr_deep(c, f);
    }
}

/// The function names one expression names where a function value is
/// expected, and whether any dynamic dispatch exists.
fn expr_calls(e: &Expr, refs: &mut HashSet<String>, saw_dyn: &mut bool) {
    match &e.e {
        E::Call { name, .. } => {
            refs.insert(name.clone());
        }
        E::FnRef(n) => {
            refs.insert(n.clone());
        }
        E::Combine { word, .. } => {
            refs.insert(word.clone());
        }
        E::ApplyEach { name, .. } => {
            refs.insert(name.clone());
        }
        E::AsDyn { .. } => {
            *saw_dyn = true;
        }
        _ => {}
    }
    for c in children(e) {
        expr_calls(c, refs, saw_dyn);
    }
}

/// The function names one function definition's body names.
fn fn_calls(
    body: &FnBody,
    default_last: Option<&Expr>,
    refs: &mut HashSet<String>,
    saw_dyn: &mut bool,
) {
    match body {
        FnBody::Expr(e) => expr_calls(e, refs, saw_dyn),
        FnBody::Block(s) => {
            for st in s.iter() {
                read_stmt_exprs(st, &mut |e| expr_calls(e, refs, saw_dyn));
            }
        }
    }
    if let Some(e) = default_last {
        expr_calls(e, refs, saw_dyn);
    }
}

// ------------------------------------------------------- dead functions

/// Remove from `prog.funcs` every function the whole program cannot reach.
/// Implementation blocks are kept whole (their dispatch is by value kind
/// at run time). Returns how many were removed.
pub fn remove_dead_funcs(prog: &mut Program) -> usize {
    let mut saw_dyn = false;
    // roots: the top-level body, every Test body, and interface call
    // names anywhere (any Call whose name matches a promise keeps ALL
    // interface impls - which stay untouched anyway).
    let mut roots: HashSet<String> = HashSet::new();
    for st in prog.body.iter() {
        read_stmt_exprs(st, &mut |e| expr_calls(e, &mut roots, &mut saw_dyn));
    }
    for t in &prog.tests {
        for st in t.body.iter() {
            read_stmt_exprs(st, &mut |e| expr_calls(e, &mut roots, &mut saw_dyn));
        }
    }
    // impl bodies are entered by dyn dispatch by value kind - keep them
    // all; their edges only ADD reachability, so count them officially
    for imp in &prog.impls {
        for f in &imp.funcs {
            let mut r = HashSet::new();
            fn_calls(&f.body, f.default_last.as_ref(), &mut r, &mut saw_dyn);
            for n in r {
                roots.insert(n);
            }
        }
        for st in imp.body.iter() {
            read_stmt_exprs(st, &mut |e| expr_calls(e, &mut roots, &mut saw_dyn));
        }
    }
    // per-function edges (names are compared lowercased: spelling of a
    // function name is caseless, as everywhere in Lykaon)
    let graph: HashMap<String, HashSet<String>> = {
        let mut m = HashMap::new();
        for f in &prog.funcs {
            let key = f.name.to_ascii_lowercase();
            let mut r = HashSet::new();
            fn_calls(&f.body, f.default_last.as_ref(), &mut r, &mut saw_dyn);
            m.insert(key, r);
        }
        m
    };
    // breadth-first reachability
    let mut alive: HashSet<String> = HashSet::new();
    let mut queue: Vec<String> = roots.iter().map(|n| n.to_ascii_lowercase()).collect();
    while let Some(n) = queue.pop() {
        if !alive.insert(n.clone()) {
            continue;
        }
        if let Some(ch) = graph.get(&n) {
            for c in ch {
                let c = c.to_ascii_lowercase();
                if !alive.contains(&c) {
                    queue.push(c);
                }
            }
        }
    }
    let before = prog.funcs.len();
    prog.funcs
        .retain(|f| f.shared || alive.contains(&f.name.to_ascii_lowercase()));
    before - prog.funcs.len()
}

// ================================================== block-body inlining
//
// (M3c-2) A multi-statement function can still be inlined when its whole
// behavior is "compute locally, hand one value back". The call site gains
// the callee's `Set` statements (locals renamed to names no source can
// spell) and its expression gains the final `Give back` expression in
// place of the call. The rules below are what keeps that rewrite
// byte-exact; each rule answers one concrete difference the naive
// substitution would make:
//
//   * fresh frame: a call runs the callee in its own Frame, so the
//     callee's locals have a lifetime of their own. Inlined Sets live in
//     the caller's frame instead - only safe because every local gets a
//     synthetic name that no source file can produce (the lexer accepts
//     words of letters and digits only, never a hyphen), so nothing the
//     caller reads later can see them.
//   * sentence state: every executed sentence that is not Combine/Apply
//     clears the caller frame's last-result for it/them. Spliced Sets are
//     sentences now, and clearing them before the call's remainder runs
//     would change what `it` means - so a statement must mention no
//     pronoun anywhere in its own expression.
//   * evaluation order: the spliced Sets run BEFORE the statement, so
//     every call input must be a leaf (a spelled value or a name). A leaf
//     reads have no side effects and cannot fail; the value is exactly
//     what the call evaluated.
//   * failure placement: a call that fails fails INSIDE the enclosing
//     Try sentence; the inlined copy would fail in a spliced statement
//     before it. Leaves cannot fail, and statements that sit inside a
//     Try sentence (the Try's own sentence) are never rewritten, so no
//     failure can move out of a catch.
//   * values with clean-up: a record built in the callee frame dies when
//     the call returns; inlined, it would live to the caller's scope end
//     and run `can clean up` late (or per iteration of a loop). Bodies
//     that build records, enums, or move/share values are refused.
//   * name resolution: a callee body may mention no name beyond its own
//     inputs and its own Set targets (each resolves in the callee frame);
//     a Set target may not double as an input (one substituted name
//     cannot be both). Anything else is refused.
//
// Statements with nested statement lists (If/Repeat/For/Look at/Try/
// Check/Test) are only WALKED into, never rewritten as wholesale
// elements: a call in a condition would need the spliced Sets before the
// whole element, and `it` inside nested arms would change meaning (the
// spliced Sets clear last-result). So the pass rewrites only simple
// sentences; everything else keeps its call.
//
// Candidates come from prog.funcs only (a function-name collision across
// impl blocks must never resolve a dispatch), no interface promise name
// is ever substituted (dyn dispatch is by value kind), and the entire
// pass is refused while any Pretend sentence stands in for a result.

/// One inlinable multi-statement function: plain local `Changeable`
/// definitions / re-assignments ending in one give back.
struct BlockCand {
    name: String,
    params: Vec<String>,
    /// body statements that compute the locals, in order
    sets: Vec<Stmt>,
    /// the final Give back expression
    final_expr: Expr,
}

fn block_has_pretend(prog: &Program) -> bool {
    fn stmts_have(sts: &[Stmt]) -> bool {
        sts.iter().any(|st| match st {
            Stmt::Pretend { .. } => true,
            Stmt::If { branches, other } => {
                branches.iter().any(|(_, b)| stmts_have(b)) || other.iter().any(|ob| stmts_have(ob))
            }
            Stmt::RepeatForever { body }
            | Stmt::RepeatTimes { body, .. }
            | Stmt::RepeatWhile { body, .. }
            | Stmt::ForRange { body, .. }
            | Stmt::ForIn { body, .. }
            | Stmt::Test { body, .. } => stmts_have(body),
            Stmt::LookAt { whens, .. } => whens.iter().any(|w| stmts_have(&w.body)),
            Stmt::Try {
                success, failure, ..
            } => stmts_have(success) || failure.iter().any(|(_, a)| stmts_have(a)),
            Stmt::Check { body, .. } => stmts_have(body),
            Stmt::DefineLocalFn(f) => {
                matches!(&f.body, FnBody::Block(s) if stmts_have(s))
            }
            _ => false,
        })
    }
    let fn_blocks: Vec<&[Stmt]> = prog
        .funcs
        .iter()
        .filter_map(|f| match &f.body {
            FnBody::Block(s) => Some(s.as_slice()),
            _ => None,
        })
        .collect();
    stmts_have(&prog.body)
        || prog.tests.iter().any(|t| stmts_have(&t.body))
        || fn_blocks.iter().any(|s| stmts_have(s))
}

/// An expression that may be copied into the CALLER's frame unchanged:
/// no calls (the callee frame resolves names), no it/them, and no value
/// whose life or ownership is tied to where it was born (records run
/// `can clean up`; give/share move ownership).
fn expr_copyable(e: &Expr) -> bool {
    if matches!(
        e.e,
        E::Call { .. }
            | E::It
            | E::Them
            | E::RecordOf { .. }
            | E::EnumOf { .. }
            | E::Move(_)
            | E::Share(_)
            | E::WeakShare(_)
    ) {
        return false;
    }
    children(e).iter().all(|c| expr_copyable(c))
}

/// Every name the expression mentions must be the function's own inputs
/// or its own Set targets; anything else resolves in the callee frame
/// (captured fixed names) and inlining would re-resolve it at the call.
fn mentions_stray(e: &Expr, legit: &HashSet<String>) -> bool {
    if let E::Name(n) = &e.e {
        if !legit.contains(n) {
            return true;
        }
    }
    children(e).iter().any(|c| mentions_stray(c, legit))
}

fn collect_block_candidates(prog: &Program) -> Vec<BlockCand> {
    fn probe(f: &sem::FuncDef, out: &mut Vec<BlockCand>) {
        if f.is_local || f.is_generator || f.can_fail {
            return;
        }
        if !f.requires.is_empty() || !f.ensures.is_empty() || f.default_last.is_some() {
            return;
        }
        let FnBody::Block(s) = &f.body else { return };
        if s.len() < 2 {
            return;
        }
        // Function bodies cannot introduce names with a bare `Set` (the
        // compile-time scope check rejects T0205), so the local state
        // statements are `Changeable <name> is <expr>.` Defines plus
        // re-assignments of names they created. Both are carried as-is.
        let mut sets: Vec<Stmt> = Vec::new();
        for st in &s[..s.len() - 1] {
            match st {
                Stmt::Set { name, expr } => {
                    sets.push(Stmt::Set {
                        name: name.clone(),
                        expr: expr.clone(),
                    });
                }
                Stmt::Define(d) => {
                    // a plain local Changeable only: not a Constant, not
                    // shared, and the fallback sentence is an outbound
                    // expression anyway (kept whole when copied)
                    if !d.mutable || d.is_const || d.shared {
                        return;
                    }
                    sets.push(st.clone());
                }
                _ => return,
            }
        }
        let Stmt::GiveBack(Some(final_expr)) = &s[s.len() - 1] else {
            return;
        };
        let params: Vec<String> = f.inputs.iter().map(|(n, _)| n.clone()).collect();
        // collect every name the body ASSIGNS (a Set target or a Define name)
        let targets: HashSet<String> = sets
            .iter()
            .map(|st| match st {
                Stmt::Set { name, .. } => name.clone(),
                Stmt::Define(d) => d.name.clone(),
                _ => unreachable!("only Set and Define are carried"),
            })
            .collect();
        let mut legit: HashSet<String> = params.iter().cloned().collect();
        for t in &targets {
            if params.contains(t) {
                return; // a target never doubles as an input
            }
            legit.insert(t.clone());
        }
        let mut ok = true;
        for st in &sets {
            let exprs: Vec<&Expr> = match st {
                Stmt::Set { expr, .. } => vec![expr],
                Stmt::Define(d) => {
                    let mut v = vec![&d.expr];
                    if let Some(fb) = &d.fallback {
                        v.push(fb);
                    }
                    v
                }
                _ => unreachable!("only Set and Define are carried"),
            };
            for ex in exprs {
                if !expr_copyable(ex) || mentions_stray(ex, &legit) {
                    ok = false;
                    break;
                }
            }
            if !ok {
                break;
            }
        }
        if !ok || !expr_copyable(final_expr) || mentions_stray(final_expr, &legit) {
            return;
        }
        out.push(BlockCand {
            name: f.name.clone(),
            params,
            sets,
            final_expr: final_expr.clone(),
        });
    }
    let mut out = Vec::new();
    for f in &prog.funcs {
        probe(f, &mut out);
    }
    out
}

/// Inline every block candidate at its call sites. Returns how many CALL
/// sites were substituted.
pub fn inline_block_bodies(prog: &mut Program) -> usize {
    if block_has_pretend(prog) {
        return 0;
    }
    let cands = collect_block_candidates(prog);
    if cands.is_empty() {
        return 0;
    }
    // interface promises dispatch by value kind at run time; a name that
    // matches any promise stays dynamic even when prog.funcs holds it
    let dyns: HashSet<String> = prog.interfaces.iter().map(|i| i.fn_name.clone()).collect();
    let subs: HashMap<String, usize> = cands
        .iter()
        .enumerate()
        .filter(|(_, c)| !dyns.contains(&c.name))
        .map(|(i, c)| (c.name.clone(), i))
        .collect();
    if subs.is_empty() {
        return 0;
    }
    let mut ctr: u32 = 0;
    let mut total = 0;
    inline_block_list(&mut prog.body, &cands, &subs, &mut ctr, &mut total);
    for f in prog.funcs.iter_mut() {
        if let FnBody::Block(s) = &mut f.body {
            inline_block_list(s, &cands, &subs, &mut ctr, &mut total);
        }
    }
    for t in prog.tests.iter_mut() {
        inline_block_list(&mut t.body, &cands, &subs, &mut ctr, &mut total);
    }
    total
}

/// Rewrite a statement list top to bottom, splicing candidate calls in
/// simple sentences, then walk into nested lists.
fn inline_block_list(
    list: &mut Vec<Stmt>,
    cands: &[BlockCand],
    subs: &HashMap<String, usize>,
    ctr: &mut u32,
    changes: &mut usize,
) {
    // NOTE: no quick reject here. A call whose callee is not a candidate
    // can still turn INTO one inside this same pass - the single-statement
    // inliner that ran just before may erase an outer call and leave its
    // (single-give-back, therefore still-nested) call body behind - so
    // correctness wins over the micro perf: walk everything.
    let mut out: Vec<Stmt> = Vec::new();
    for st in list.drain(..) {
        let mut st = st;
        let mut tmps: Vec<Stmt> = Vec::new();
        rewrite_simple(&mut st, cands, subs, ctr, changes, &mut tmps);
        out.extend(tmps);
        out.push(st);
    }
    for st in out.iter_mut() {
        inline_block_nested(st, cands, subs, ctr, changes);
    }
    *list = out;
}

/// Statements the pass walks into but never rewrites as whole elements.
fn stmt_is_nested(st: &Stmt) -> bool {
    matches!(
        st,
        Stmt::If { .. }
            | Stmt::RepeatForever { .. }
            | Stmt::RepeatTimes { .. }
            | Stmt::RepeatWhile { .. }
            | Stmt::ForRange { .. }
            | Stmt::ForIn { .. }
            | Stmt::LookAt { .. }
            | Stmt::Try { .. }
            | Stmt::Test { .. }
            | Stmt::Check { .. }
            | Stmt::DefineLocalFn(_) // a closure body: walk in, no element rewrite
    )
}

/// A leaf call input: read has no side effects and cannot fail, so it may
/// be evaluated early (inside the spliced Sets) or read once more.
fn is_leaf_arg(a: &Expr) -> bool {
    matches!(
        a.e,
        E::Whole(_) | E::Dec(_) | E::Boolean(_) | E::Word(_) | E::Missing | E::Name(_)
    )
}

/// Substitute a call's leaf inputs for the body's input names, bottom
/// (leaf) up. A parameter only appears as a leaf name, so one pass is
/// enough and no recursion descends into a replaced input.
fn subst_leaf_params(e: &mut Expr, params: &[String], args: &[Expr]) {
    if let E::Name(n) = &e.e {
        if let Some(i) = params.iter().position(|p| p == n) {
            *e = args[i].clone();
            return;
        }
    }
    for child in crate::optimizer::children_mut(e) {
        subst_leaf_params(child, params, args);
    }
}

/// Rename the callee's locals to their synthetic site names (targets are
/// disjoint from the inputs, so the two renames cannot collide).
fn rename_locals(e: &mut Expr, map: &HashMap<String, String>) {
    let hit = match &e.e {
        E::Name(n) => map.get(n).cloned(),
        _ => None,
    };
    if let Some(nn) = hit {
        let kind = e.kind.clone();
        let dis = e.dis.clone();
        let can_fail = e.can_fail;
        let num_word = e.num_word;
        *e = Expr {
            kind,
            e: E::Name(nn.clone()),
            dis,
            can_fail,
            num_word,
        };
        return;
    }
    for child in crate::optimizer::children_mut(e) {
        rename_locals(child, map);
    }
}

/// The expressions the statement itself carries (deep), not nested
/// statement bodies (those are separate sentences with their own state).
fn own_exprs_mut_for_probe(st: &mut Stmt, f: &mut dyn FnMut(&mut Expr)) {
    map_deep_expr(st_exprs_mut(st), f);
}

fn st_exprs_mut(st: &mut Stmt) -> Vec<&mut Expr> {
    match st {
        Stmt::Note | Stmt::Stop | Stmt::Skip | Stmt::PassFailureUp
        | Stmt::Share { .. } | Stmt::Use { .. } | Stmt::Close { .. }
        | Stmt::RemoveFirst { .. } | Stmt::DefineEnum { .. }
        | Stmt::DefineLocalFn(_) | Stmt::GiveBack(None)
        | Stmt::RepeatForever { .. }
        // M4 (Appendix K) task sentences hold no own expressions; their
        // bodies stay whole like a Check/Test front.
        | Stmt::StartTask { .. } | Stmt::WaitFor { .. } | Stmt::DoTogether { .. }
        | Stmt::StopTask { .. } | Stmt::SleepFor { .. }
        // M4-4: timer/stream sentences hold no own expressions either
        // (Use N workers. carries a counted literal, not an expression).
        // M4-7: Use seed. carries a seed literal, not an expression.
        | Stmt::AfterTimer { .. } | Stmt::EveryTimer { .. }
        | Stmt::StreamLoop { .. } | Stmt::UseWorkers { .. }
        | Stmt::UseSeed { .. }
        // Receive holds only the channel name
        | Stmt::Receive { .. } => Vec::new(),
        // M4 (Appendix K): Send/AtomicAdd carry the value expression
        Stmt::Send { value, .. } | Stmt::AtomicAdd { value, .. } => vec![value],
        // M4-4: a spread's own expression is its items value
        Stmt::Spread { items, .. } => vec![items],
        Stmt::Define(d) => {
            let mut v = vec![&mut d.expr];
            if let Some(fb) = &mut d.fallback {
                v.push(fb);
            }
            v
        }
        Stmt::Set { expr, .. } | Stmt::Say { expr, .. } | Stmt::Evaluate { expr, .. } => {
            vec![expr]
        }
        Stmt::Ask { fallback, .. } => match fallback {
            Some(e) => vec![e],
            None => Vec::new(),
        },
        Stmt::If { branches, .. } => branches.iter_mut().map(|(c, _)| c).collect(),
        Stmt::RepeatTimes { count, .. } | Stmt::RepeatWhile { cond: count, .. } => vec![count],
        Stmt::ForRange { from, to, .. } => vec![from, to],
        Stmt::ForIn { list, .. } => vec![list],
        Stmt::Append { value, .. } => vec![value],
        Stmt::Put { key, value, .. } => match key {
            Some(k) => vec![k, value],
            None => vec![value],
        },
        Stmt::Remove { value, .. } => vec![value],
        Stmt::SetPart { expr, .. } => vec![expr],
        Stmt::LookAt { value, .. } => vec![value],
        Stmt::Fail { message } => vec![message],
        Stmt::Pretend { value, .. } => vec![value],
        Stmt::GiveBack(Some(e)) => vec![e],
        Stmt::HandBack(e) => vec![e],
        // Try's sentence holds other statements' Try semantics; Check and
        // Test only carry nested lists; the fronts of those stay whole.
        Stmt::Try { .. } | Stmt::Check { .. } | Stmt::Test { .. } => Vec::new(),
        // M4-5 (Appendix K 7.5): the write/append/replace value is front
        // material; the other file sentences hold only literal path
        // words, and their bodies are walked by the list walker.
        Stmt::WriteFile { value, .. } | Stmt::AppendFile { value, .. }
        | Stmt::ReplaceFile { value, .. }
        | Stmt::SaveFormat { value, .. } | Stmt::ReadFormatText { value, .. } => vec![value],
        Stmt::ReadFile { .. } | Stmt::ReadBytes { .. } | Stmt::ListFolder { .. }
        | Stmt::MakeFolder { .. } | Stmt::RemovePath { .. } | Stmt::MovePath { .. }
        | Stmt::DuplicatePath { .. } | Stmt::MakeTempFile { .. }
        | Stmt::ZipOp { .. } | Stmt::ReadFormat { .. }
        | Stmt::ForEachLine { .. } | Stmt::WhenFileChanges { .. }
        // M4-7 (7.7): Use seed holds no expression.
        | Stmt::UseSeed { .. }
        // M4-8 (7.10/7.11): the signal and input loop bodies are walked by
        // the list walker; Exit carries only a literal code.
        | Stmt::WhenSignal { .. } | Stmt::ForEachInput { .. }
        | Stmt::Exit { .. } => Vec::new(),
        // M4-8: the Run arguments are front expressions (like a Send's)
        Stmt::RunProc { args, .. } => args.iter_mut().collect(),
        // M4-9 (7.12): the Log text is a front expression (like a Say's)
        Stmt::Log { expr, .. } => vec![expr],
        Stmt::LogLevel { .. } => Vec::new(),
        // M4-10 (7.8): the fetch/post/send values are front expressions;
        // the Respond values are; the server bodies are walked by the
        // list walker
        Stmt::Fetch { data, headers, query, .. } => {
            let mut out: Vec<&mut Expr> = Vec::new();
            if let Some(d) = data {
                out.push(d);
            }
            out.extend(headers.iter_mut().map(|(_, e)| e));
            out.extend(query.iter_mut().map(|(_, e)| e));
            out
        }        Stmt::PostTo { data, .. } => vec![data],
        Stmt::WsSend { value } => vec![value],
        Stmt::Respond { kind, .. } => match kind {
            sem::RespondKind::Text(e) | sem::RespondKind::Json(e)
            | sem::RespondKind::Literally(e) => vec![e],
            sem::RespondKind::Status(_, Some(e)) => vec![e],
            sem::RespondKind::Status(_, None) | sem::RespondKind::Template(_) => Vec::new(),
        },
        Stmt::Serve { .. } | Stmt::WhenSomeone { .. } | Stmt::WhenLive { .. }
        | Stmt::PageDecl { .. } | Stmt::WsRecv { .. } => Vec::new(),
        Stmt::Careful { .. } => Vec::new(),
    }
}

fn map_deep_expr(list: Vec<&mut Expr>, f: &mut dyn FnMut(&mut Expr)) {
    for e in list {
        map_deep(e, f);
    }
}

fn map_deep(e: &mut Expr, f: &mut dyn FnMut(&mut Expr)) {
    for c in crate::optimizer::children_mut(e) {
        map_deep(c, f);
    }
    f(e);
}

/// Rewrite one simple sentence: replace every safe candidate call inside
/// its own expressions with the callee's Sets (renamed, spliced) and the
/// final give back expression. Returns the spliced Sets via `out`.
fn rewrite_simple(
    st: &mut Stmt,
    cands: &[BlockCand],
    subs: &HashMap<String, usize>,
    ctr: &mut u32,
    changes: &mut usize,
    out: &mut Vec<Stmt>,
) {
    if stmt_is_nested(st) {
        return;
    }
    // spliced Sets clear the caller frame's last-result; a pronoun read
    // in this statement would then see the wrong reference - refuse
    let mut pronoun = false;
    own_exprs_mut_for_probe(st, &mut |e| {
        if matches!(e.e, E::It | E::Them) {
            pronoun = true;
        }
    });
    if pronoun {
        return;
    }
    let lists = st_exprs_mut(st);
    for holder in lists {
        rewrite_deep(holder, cands, subs, ctr, changes, out);
    }
}

fn rewrite_deep(
    e: &mut Expr,
    cands: &[BlockCand],
    subs: &HashMap<String, usize>,
    ctr: &mut u32,
    changes: &mut usize,
    out: &mut Vec<Stmt>,
) {
    for child in crate::optimizer::children_mut(e) {
        rewrite_deep(child, cands, subs, ctr, changes, out);
    }
    if let E::Call { name, args } = &mut e.e {
        let Some(&ci) = subs.get(name) else { return };
        if args.len() != cands[ci].params.len() {
            return;
        }
        if !args.iter().all(|a| is_leaf_arg(a)) {
            return;
        }
        let tag = {
            *ctr += 1;
            *ctr
        };
        let cand = &cands[ci];
        // the callee's locals become site-unique names no source can
        // spell (the lexer accepts letters and digits only)
        let rename: HashMap<String, String> = cand
            .sets
            .iter()
            .map(|st| match st {
                Stmt::Set { name, .. } => (name.clone(), format!("inl-{tag}-{name}")),
                Stmt::Define(d) => (d.name.clone(), format!("inl-{tag}-{}", d.name)),
                _ => unreachable!("only Set and Define are carried"),
            })
            .collect();
        for st in &cand.sets {
            let mut st = st.clone();
            match &mut st {
                // re-assignments keep their (renamed) scope slot name
                Stmt::Set { name, expr } => {
                    subst_leaf_params(expr, &cand.params, args);
                    rename_locals(expr, &rename);
                    if let Some(nn) = rename.get(name) {
                        *name = nn.clone();
                    }
                }
                Stmt::Define(d) => {
                    subst_leaf_params(&mut d.expr, &cand.params, args);
                    rename_locals(&mut d.expr, &rename);
                    if let Some(fb) = &mut d.fallback {
                        subst_leaf_params(fb, &cand.params, args);
                        rename_locals(fb, &rename);
                    }
                    if let Some(nn) = rename.get(&d.name) {
                        d.name = nn.clone();
                    }
                }
                _ => unreachable!("only Set and Define are carried"),
            }
            out.push(st);
        }
        let mut repl = cand.final_expr.clone();
        subst_leaf_params(&mut repl, &cand.params, args);
        rename_locals(&mut repl, &rename);
        *e = repl;
        *changes += 1;
    }
}

/// Walk into the nested statement lists of one statement.
fn inline_block_nested(
    st: &mut Stmt,
    cands: &[BlockCand],
    subs: &HashMap<String, usize>,
    ctr: &mut u32,
    changes: &mut usize,
) {
    match st {
        Stmt::If { branches, other } => {
            for (_, b) in branches.iter_mut() {
                inline_block_list(b, cands, subs, ctr, changes);
            }
            if let Some(ob) = other {
                inline_block_list(ob, cands, subs, ctr, changes);
            }
        }
        Stmt::RepeatForever { body }
        | Stmt::RepeatTimes { body, .. }
        | Stmt::RepeatWhile { body, .. }
        | Stmt::ForRange { body, .. }
        | Stmt::ForIn { body, .. }
        | Stmt::Test { body, .. } => {
            inline_block_list(body, cands, subs, ctr, changes);
        }
        Stmt::LookAt { whens, .. } => {
            for w in whens.iter_mut() {
                inline_block_list(&mut w.body, cands, subs, ctr, changes);
            }
        }
        // the Try sentence stays whole: a failure in the call is caught
        // here, and an inlined copy would have to run outside the catch
        Stmt::Try {
            success, failure, ..
        } => {
            inline_block_list(success, cands, subs, ctr, changes);
            for (_, arms) in failure.iter_mut() {
                inline_block_list(arms, cands, subs, ctr, changes);
            }
        }
        Stmt::Check { body, .. } => {
            inline_block_list(body, cands, subs, ctr, changes);
        }
        Stmt::DefineLocalFn(f) => {
            if let FnBody::Block(s) = &mut f.body {
                inline_block_list(s, cands, subs, ctr, changes);
            }
        }
        _ => {}
    }
}

// ============================================== cross-package constants
//
// (M3c-3) A top-level immutable definition (the `Constant <n> is <v>.`
// sentence, and equally the plain `<n> is <v>.` sentence - both parse to
// a Decl with mutable == false) whose value is a LEAF LITERAL is the
// same value every time it is read after its sentence ran. Replacement
// of the read name with the literal is then pure bookkeeping - the read
// already resolved through the frame and found exactly that value. The
// soundness notes below are why the first cut stays narrow:
//
//   * statement ORDER is the runtime order at the top level: a constant
//     defined at statement index d is visible in the top-level frame
//     from index d + 1 on. Reads in statements at index <= d would see
//     Missing (or nothing - the scoper rejects them statically, T0205),
//     so ONLY statements AFTER the definition get folded, by statement
//     index, including the nested lists inside them (they execute during
//     the statement, strictly after).
//   * FUNCTIONS are NOT folded in this cut: a function reads a fixed
//     top-level value through its CAPTURES, seeded at CALL time from the
//     caller's frame. A call that runs before the constant's statement
//     has executed would read Missing out of an unseeded capture, and a
//     folded body would read the value instead - a real behavior change
//     even though the shape is rare. Widening needs call-site style
//     analysis and is logged for later.
//   * TESTS are NOT folded: run_test starts a FRESH frame and never
//     executes prog.body first, so a test reading a top-level constant
//     name reports a Missing-like value today; folding would change it.
//   * CLOSURES inside folded statements are excluded: a closure body can
//     outlive the statement and run much later.
//   * the value must be a leaf literal (whole/decimal/yes-no/word/
//     missing) with no can_fail text: those reads never fail, never
//     print, and never construct anything with clean-up or ownership
//     bookkeeping, so the copy is unobservable.
//
// The tree is the whole program (Use files are flattened into one source
// before parsing), so these top-level constants come from EVERY package
// at once - the pass name is about the view, not a per-package walk.

/// Fold top-level immutable known values into later name reads. Returns
/// how many name reads were replaced.
pub fn propagate_constants(prog: &mut Program) -> usize {
    // name -> (statement index of the definition, literal value)
    let mut known: HashMap<String, (usize, Expr)> = HashMap::new();
    for (i, st) in prog.body.iter().enumerate() {
        if let Stmt::Define(d) = st {
            if d.mutable {
                continue;
            }
            // a leaf literal whose copies can never be observed otherwise
            if !is_leaf_arg(&d.expr) || !expr_copyable(&d.expr) {
                continue;
            }
            known.insert(d.name.clone(), (i, d.expr.clone()));
        }
    }
    if known.is_empty() {
        return 0;
    }
    let mut total = 0;
    for i in 0..prog.body.len() {
        // only the values defined strictly before this statement
        let active: Vec<(String, Expr)> = known
            .iter()
            .filter(|(_, (di, _))| *di < i)
            .map(|(n, (_, e))| (n.clone(), e.clone()))
            .collect();
        if active.is_empty() {
            continue;
        }
        let st = &mut prog.body[i];
        if matches!(st, Stmt::DefineLocalFn(_)) {
            continue;
        }
        for ex in st_exprs_mut(st) {
            fold_const_expr(ex, &active, &mut total);
        }
        fold_const_nested(st, &active, &mut total);
    }
    total
}

/// Replace name reads with the known literal, bottom (leaf) up. The copy
/// carries all five Expr fields (kind for downstream decisions, dis for
/// diagnostics, can_fail/num_word for the text rules) exactly as the
/// single-statement inliner clones bodies wholesale.
fn fold_const_expr(e: &mut Expr, active: &[(String, Expr)], total: &mut usize) {
    let hit = match &e.e {
        E::Name(n) => active.iter().find(|(nn, _)| nn == n),
        _ => None,
    };
    if let Some((_, c)) = hit {
        let kind = c.kind.clone();
        let ene = c.e.clone();
        let dis = c.dis.clone();
        let can_fail = c.can_fail;
        let num_word = c.num_word;
        *e = Expr {
            kind,
            e: ene,
            dis,
            can_fail,
            num_word,
        };
        *total += 1;
        return;
    }
    for child in crate::optimizer::children_mut(e) {
        fold_const_expr(child, active, total);
    }
}

/// Walk nested lists of one top-level statement (closures never touched).
fn fold_const_nested(st: &mut Stmt, active: &[(String, Expr)], total: &mut usize) {
    match st {
        Stmt::If { branches, other } => {
            for (_, b) in branches.iter_mut() {
                fold_const_list(b, active, total);
            }
            if let Some(ob) = other {
                fold_const_list(ob, active, total);
            }
        }
        Stmt::RepeatForever { body }
        | Stmt::RepeatTimes { body, .. }
        | Stmt::RepeatWhile { body, .. }
        | Stmt::ForRange { body, .. }
        | Stmt::ForIn { body, .. } => {
            fold_const_list(body, active, total);
        }
        // Note: no Test arm on purpose - tests run on a fresh frame that
        // never executed the top-level Define statements, so a top-level
        // constant name inside a test body does NOT read this value.
        Stmt::LookAt { whens, .. } => {
            for w in whens.iter_mut() {
                fold_const_list(&mut w.body, active, total);
            }
        }
        Stmt::Try {
            success, failure, ..
        } => {
            fold_const_list(success, active, total);
            for (_, arms) in failure.iter_mut() {
                fold_const_list(arms, active, total);
            }
        }
        Stmt::Check { body, .. } => {
            fold_const_list(body, active, total);
        }
        _ => {}
    }
}

fn fold_const_list(list: &mut Vec<Stmt>, active: &[(String, Expr)], total: &mut usize) {
    for st in list.iter_mut() {
        if matches!(st, Stmt::DefineLocalFn(_)) {
            continue;
        }
        for ex in st_exprs_mut(st) {
            fold_const_expr(ex, active, total);
        }
        fold_const_nested(st, active, total);
    }
}
