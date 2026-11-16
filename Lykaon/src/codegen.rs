//! Cranelift native codegen for Lykaon (M3).
//!
//! Two real build behaviours (no stubs):
//!
//! * `Full`: every function and the top-level body lower to Cranelift machine
//!   code. Scalar values are unboxed (`whole` as i64, `decimal` as f64,
//!   `yes or no` as i8 0/1). Whole-number arithmetic keeps the interpreter's
//!   checked semantics (T0603 on overflow, T0604 on division by zero), and
//!   output is buffered by the runtime and printed once at program end, so an
//!   interrupted run prints the error line alone, exactly like `lykaon run`.
//!   Every lowered function carries a hidden depth parameter so deep
//!   recursion stops with the interpreter's T0607 (calls nested past 240).
//!
//! * `Embedded`: the program uses kinds the scalar backend does not lower in
//!   M3 (texts, lists, maps, records, generators, closures, contracts...).
//!   The emitted object carries the source as a `lykaon_src` data symbol and a
//!   `lykaon_main` that calls `lykaon_rt_main` in liblykaon_rt, which compiles the
//!   embedded source with the same front-end the developer used and executes
//!   it with the evaluator of lykaon-core — the interpreter that "defines what
//!   every program means" (ch.33). This makes the differential guarantee
//!   (native output equals interpreter output, byte for byte) hold by
//!   construction, and runs contracts exactly as the interpreter does,
//!   honouring the build mode (M3-S37: removed in fast/small unless
//!   `checked`).
//!
//! The Full path walks the typed tree, whose nesting mirrors the
//! interpreter's frames exactly; a scope is pushed for each branch or loop
//! body and popped on exit, so every name lookup resolves the way
//! `Frame.find`/`Frame.assign` do. Windows x86-64: every function uses the
//! Microsoft x64 convention (CallConv::WindowsFastcall); Linux x86-64: System
//! V (M3 section 9). The MIR graph remains the instruction-set artifact the
//! optimizer contracts (book section 8) name; optimizer pass reports say
//! which passes fired.
//!
//! Exactness notes that keep native == interpreter:
//! - `is`/`is not` on two decimals gives `no`: cmp_eq has no (Dec, Dec) arm
//!   in the interpreter, so the backend folds it to a constant (and still
//!   evaluates both operands first, since they may print or fail).
//! - Ordering comparisons convert whole values to f64 (cmp_ord's numeric
//!   path); NaN compares as equal, so `at least` / `at most` use the
//!   unordered-or-... float conditions (true on NaN).
//! - `Repeat times` evaluates the limit once; the counter starts at 1 and
//!   increments with saturating +1 after each pass (interp.rs).
//! - `Set` on an undefined name defines it into the last scope
//!   (Frame.assign's fallback), exactly like the interpreter.
//! - Falling off the end of a function gives `missing` in the evaluator, so
//!   the control-flow scanner (`always_gives`) only accepts functions whose
//!   every path ends in a give back; zero-pass loops never count.

use crate::sem::{self, Comp, E, Expr, Op, Rel};

use cranelift_codegen::Context;
use cranelift_codegen::ir;
use cranelift_codegen::ir::InstBuilder;
use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::immediates::Ieee64;
use cranelift_codegen::ir::{Function, Signature, UserFuncName};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataId, FuncId, Linkage, Module};
use cranelift_native::builder as native_builder;
use cranelift_object::{ObjectBuilder, ObjectModule};

const WORD: ir::Type = ir::types::I64;
const FLT: ir::Type = ir::types::F64;
const BOOL: ir::Type = ir::types::I8;
const RET: ir::Type = ir::types::I32;

/// Build mode handed to the runtime (M3-S37): 0 debug, 1 fast, 2 small.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BuildMode {
    Debug,
    Fast,
    Small,
}

impl BuildMode {
    pub fn code(self) -> i64 {
        match self {
            BuildMode::Debug => 0,
            BuildMode::Fast => 1,
            BuildMode::Small => 2,
        }
    }
    fn from_str(s: &str) -> BuildMode {
        match s {
            "fast" => BuildMode::Fast,
            "small" => BuildMode::Small,
            _ => BuildMode::Debug,
        }
    }
}

/// Which native backend the program receives, with the honest reason when
/// the scalar path does not apply (reported by `--report`).
#[derive(Debug, Clone, PartialEq)]
pub enum LowerKind {
    /// The whole program is lowered to Cranelift machine code.
    Full,
    /// `lykaon_main` runs the embedded source through the evaluator of lykaon-core.
    Embedded { reason: String },
}

/// What one scalar value looks like in registers.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Scalar {
    Whole,   // i64
    Decimal, // f64
    Boolean, // i8 0/1
}

impl Scalar {
    fn ty(self) -> ir::Type {
        match self {
            Scalar::Whole => WORD,
            Scalar::Decimal => FLT,
            Scalar::Boolean => BOOL,
        }
    }
}

fn kind_scalar(kind: &sem::Kind) -> Option<Scalar> {
    match kind {
        sem::Kind::Whole => Some(Scalar::Whole),
        sem::Kind::Decimal => Some(Scalar::Decimal),
        sem::Kind::Boolean => Some(Scalar::Boolean),
        _ => None,
    }
}

// ================================================================ analysis

pub fn classify(prog: &sem::Program) -> LowerKind {
    match scan_program(prog) {
        Ok(_) => LowerKind::Full,
        Err(reason) => LowerKind::Embedded { reason },
    }
}

/// A local function (closure, ch.24) planned for machine lowering: the def,
/// the free names its body reads resolved against the defining walk's
/// scopes (the interpreter's DefineLocalFn snapshot), and one result kind.
#[derive(Clone)]
pub struct CFnPlan {
    pub name: String,
    pub def: sem::FuncDef,
    pub caps: Vec<(String, Scalar)>,
    pub ret: Scalar,
}

/// Names visible to a scan: every callable (top-level functions plus
/// closures already defined), and, while a closure body is under scan, the
/// free names it reads (the capture snapshot it will receive). All Fx
/// instances of one scan share the closure-plan list.
struct Fx {
    fns: std::collections::HashSet<String>,
    caps: std::cell::RefCell<std::collections::BTreeMap<String, ()>>,
    allow_caps: bool,
    plans: std::rc::Rc<std::cell::RefCell<Vec<CFnPlan>>>,
    /// result kinds learned while scanning: stated kinds for block bodies,
    /// derived kinds for one-line expression bodies (no stated kind is
    /// needed — the scan computes the expression's kind). All Fx instances
    /// of one scan share this map, so a call from the main body to a small
    /// helper defined earlier resolves its kind here.
    kinds: std::rc::Rc<std::cell::RefCell<std::collections::BTreeMap<String, Scalar>>>,
    /// the defining walk's name kinds at the point the closure was written
    /// (outermost scope LAST), for one walk only: a free read inside the
    /// closure body takes its captured kind from here, because the sem
    /// usually knows no kind for a plain name read
    /// (kind from here)
    cap_kinds: std::rc::Rc<Vec<(String, Scalar)>>,
}

/// What the scan produces for the machine path: the top-level functions to
/// lower (program order, with one result kind each), the closure machines
/// of the top-level body, and the result kind of every callable learned so
/// far (used by the emitter's kind queries).
pub struct ScanOut {
    pub lowers: Vec<(usize, Scalar)>,
    pub plans: Vec<CFnPlan>,
    pub kinds: std::collections::BTreeMap<String, Scalar>,
}

impl Fx {
    fn new(
        fns: std::collections::HashSet<String>,
        kinds: std::rc::Rc<std::cell::RefCell<std::collections::BTreeMap<String, Scalar>>>,
    ) -> Self {
        Fx {
            fns,
            caps: std::cell::RefCell::new(std::collections::BTreeMap::new()),
            allow_caps: false,
            plans: std::rc::Rc::new(std::cell::RefCell::new(Vec::new())),
            kinds,
            cap_kinds: std::rc::Rc::new(Vec::new()),
        }
    }
    /// A closure body's scan inherits all callables and records fresh caps;
    /// the plan list and the kinds map are shared with the parent scan. The
    /// closure's free reads resolve their kinds against the defining walk
    /// (passed in flat, outermost scope LAST — lookup order preserved).
    fn for_closure(outer: &Fx, flat: Vec<(String, Scalar)>) -> Self {
        Fx {
            fns: outer.fns.clone(),
            caps: std::cell::RefCell::new(std::collections::BTreeMap::new()),
            allow_caps: true,
            plans: outer.plans.clone(),
            kinds: outer.kinds.clone(),
            cap_kinds: std::rc::Rc::new(flat),
        }
    }
    fn call_plan(&self, _prog: &sem::Program, name: &str) -> Option<CFnPlan> {
        self.plans.borrow().iter().find(|p| p.name == name).cloned()
    }
}

/// Feature gates shared by both function shapes: things the scalar backend
/// cannot lower in M3 (ch.25 generators, ch.18 can-fail, ch.64 contracts,
/// ch.15 defaulting inputs, a local To is not a top-level function) and the
/// M3-S9 stated scalar input kinds.
fn fn_shape_gate(f: &sem::FuncDef) -> Result<(), String> {
    let bad = |what: &str| Err(format!("the function '{}' {what}", f.name));
    if f.is_generator {
        return bad(
            "is a generator (ch.25); the scalar backend lowers number functions only in M3",
        );
    }
    if f.can_fail {
        return bad("can fail; can-fail functions run through the evaluator in M3");
    }
    if !f.requires.is_empty() || !f.ensures.is_empty() {
        return bad("states contracts (ch.64); contract functions run through the evaluator in M3");
    }
    if f.default_last.is_some() {
        return bad("uses a defaulting-to input (ch.15)");
    }
    if f.is_local {
        return bad("is a local function (closure, ch.24)");
    }
    for t in &f.input_types {
        let Some(sem::ParamType::K(k)) = t else {
            return bad(
                "takes an input with no stated kind (M3-S9: it runs through the evaluator in M3)",
            );
        };
        if kind_scalar(k).is_none() {
            return bad("takes a kind the scalar backend does not lower in M3");
        }
    }
    Ok(())
}

fn fn_shape_ok(f: &sem::FuncDef) -> Result<Scalar, String> {
    let bad = |what: &str| Err(format!("the function '{}' {what}", f.name));
    fn_shape_gate(f)?;
    // Block bodies only here; a one-line expression body takes the gate
    // above and derives its result kind from the scan (stage 2).
    if !matches!(&f.body, sem::FnBody::Block(_)) {
        return bad(
            "is written on one line without a stated result kind (as ...); M3 lowers it through the evaluator",
        );
    }
    // M3-S9: the Full path needs one concrete result kind. The sem records
    // an explicit `as <kind>` on the give back when one is stated; there
    // every Give back already carries a static kind, so the function takes
    // that kind when all give backs agree, and takes the embedded path
    // (where the evaluator answers per instance) when they differ.
    let Some(result) = fn_result_scalar(f) else {
        return bad("does not state one result kind (M3-S9: it runs through the evaluator in M3)");
    };
    Ok(result)
}

/// The function's result kind, as above.
fn fn_result_scalar(f: &sem::FuncDef) -> Option<Scalar> {
    if let Some(sem::ParamType::K(k)) = &f.result_type {
        return kind_scalar(k);
    }
    let stmts = match &f.body {
        sem::FnBody::Block(s) => s,
        _ => return None,
    };
    let mut kinds: Vec<Scalar> = Vec::new();
    collect_give_kinds(stmts, &mut kinds);
    if kinds.is_empty() {
        return None;
    }
    if kinds.iter().any(|k| *k != kinds[0]) {
        return None;
    }
    Some(kinds[0])
}

fn collect_give_kinds(stmts: &[sem::Stmt], kinds: &mut Vec<Scalar>) {
    for s in stmts {
        match s {
            sem::Stmt::GiveBack(Some(e)) => {
                if let Some(k) = kind_scalar(&e.kind) {
                    kinds.push(k);
                }
            }
            sem::Stmt::If { branches, other } => {
                for (_, b) in branches {
                    collect_give_kinds(b, kinds);
                }
                if let Some(ob) = other {
                    collect_give_kinds(ob, kinds);
                }
            }
            sem::Stmt::RepeatTimes { body, .. }
            | sem::Stmt::RepeatForever { body }
            | sem::Stmt::RepeatWhile { body, .. }
            | sem::Stmt::ForRange { body, .. }
            | sem::Stmt::ForIn { body, .. } => {
                collect_give_kinds(body, kinds);
            }
            _ => {}
        }
    }
}

/// Does this statement list always end with a `Give back` of a value on
/// every path the interpreter could take? Falling off the end of a function
/// body yields `missing` in interp.rs (`Ok(_) => Ok(Value::Missing)`), so a
/// path that could fall through must not count.
fn always_gives(stmts: &[sem::Stmt]) -> bool {
    for st in stmts {
        match st {
            sem::Stmt::GiveBack(Some(_)) => return true, // ends the path; later statements are unreachable
            sem::Stmt::GiveBack(None) => return false,   // gives `missing`, not a scalar path
            sem::Stmt::Stop | sem::Stmt::Skip => return false, // escapes with no value
            sem::Stmt::If { branches, other } => {
                // the give back only ends the path when every branch gives AND
                // an otherwise exists and gives (without one, an untaken set
                // of branches falls through and the function gives `missing`)
                if let Some(ob) = other {
                    if !branches.is_empty()
                        && branches.iter().all(|(_, b)| always_gives(b))
                        && always_gives(ob)
                    {
                        return true;
                    }
                }
                // otherwise fall through and check the later statements
            }
            // A give back inside a loop does not guarantee one: the loop may
            // run zero passes (`Repeat 0 times`, `Repeat while no ...`, For
            // from 5 to 4), and then the interpreter gives `missing`.
            _ => {}
        }
    }
    false
}

fn scan_program(prog: &sem::Program) -> Result<ScanOut, String> {
    if std::env::var_os("Lykaon_DEBUG_SCAN").is_some() {
        eprintln!(
            "scan: funcs=[{:?}]",
            prog.funcs
                .iter()
                .map(|f| f.name.clone())
                .collect::<Vec<_>>()
        );
        for (i, f) in prog.funcs.iter().enumerate() {
            eprintln!(
                "scan: fn[{i}] '{}' is_local={} body={}",
                f.name,
                f.is_local,
                match &f.body {
                    sem::FnBody::Block(_) => "block",
                    sem::FnBody::Expr(_) => "expr",
                }
            );
        }
    }
    // A To inside a block is ALSO hoisted into prog.funcs by the sem
    // (hoist_rec recurses through the tree), so every local function exists
    // twice: a hoisted copy and the Stmt::DefineLocalFn of the walk. The
    // interpreter calls the closure value in scope first and prog.funcs
    // second (interp.rs eval_call_values), and a top-level function body
    // can never legally see a caller's frame — so the machine path lowers
    // only the DefineLocalFn copy and skips the hoisted names as functions.
    let mut local_names: std::collections::HashSet<String> = std::collections::HashSet::new();
    local_fn_names(&prog.body, &mut local_names);
    // Stage 1: which functions are scalar-shaped; every function must be,
    // or the evaluator takes the whole program (M3-D6). Self-recursion is
    // fine. A one-line expression body (ch.15 `give ...`) is allowed: its
    // result kind is derived from the expression itself in stage 2, where
    // every call it makes must already have a resolvable kind (stated, or
    // derived by an earlier scan in program order).
    let mut lowers: Vec<(usize, Scalar)> = Vec::new();
    let kinds_shared: std::rc::Rc<std::cell::RefCell<std::collections::BTreeMap<String, Scalar>>> =
        std::rc::Rc::new(std::cell::RefCell::new(std::collections::BTreeMap::new()));
    for (i, f) in prog.funcs.iter().enumerate() {
        if local_names.contains(&f.name) {
            continue; // the DefineLocalFn machinery lowers this one
        }
        fn_shape_gate(f).map_err(|e| format!("{e}"))?;
        match &f.body {
            sem::FnBody::Block(_) => {
                let k = fn_shape_ok(f)?;
                lowers.push((i, k));
                kinds_shared.borrow_mut().insert(f.name.clone(), k);
            }
            sem::FnBody::Expr(_) => {} // kind derived in stage 2
        }
    }
    let names: std::collections::HashSet<String> =
        prog.funcs.iter().map(|f| f.name.to_string()).collect();

    // Stage 2: every body must scan clean.
    for (i, f) in prog.funcs.iter().enumerate() {
        if local_names.contains(&f.name) {
            continue; // lowered from the DefineLocalFn statement instead
        }
        let mut scopes: Vec<Vec<(String, Scalar)>> = vec![Vec::new()];
        for (j, t) in f.input_types.iter().enumerate() {
            let Some(sem::ParamType::K(k)) = t else {
                unreachable!()
            };
            let k = kind_scalar(k).ok_or_else(|| "bad kind".to_string())?;
            scopes[0].push((f.inputs[j].0.clone(), k));
        }
        let mut fx = Fx::new(names.clone(), kinds_shared.clone());
        match &f.body {
            sem::FnBody::Block(stmts) => {
                if !always_gives(stmts) {
                    return Err(format!(
                        "the function '{}' does not give back on every path; the evaluator runs it in M3",
                        f.name
                    ));
                }
                scan_stmts(prog, stmts, &mut scopes, true, &mut fx)
                    .map_err(|e| format!("the function '{}': {}", f.name, e))?;
                // A local function inside a top-level function captures that
                // function's frame, which no caller can supply: the evaluator
                // runs it in M3 (same reasoning as M3-D2).
                if !fx.plans.borrow().is_empty() {
                    return Err(format!(
                        "a local function (closure) defined inside '{}' needs call-site state the scalar backend does not lower in M3",
                        f.name
                    ));
                }
            }
            sem::FnBody::Expr(e) => {
                let k = scan_expr(prog, e, &scopes, &fx)
                    .map_err(|err| format!("the function '{}': {err}", f.name))?;
                kinds_shared.borrow_mut().insert(f.name.clone(), k);
                lowers.push((i, k));
            }
        }
    }
    // Top-level body: scopes start empty, so a read of a name before its
    // definition is rejected here (the interpreter's T0205) and the program
    // takes the embedded path where the evaluator says the same words.
    let mut scopes: Vec<Vec<(String, Scalar)>> = vec![Vec::new()];
    let mut fx = Fx::new(names, kinds_shared.clone());
    scan_stmts(prog, &prog.body, &mut scopes, false, &mut fx)?;
    let plans = fx.plans.borrow().clone();
    Ok(ScanOut {
        lowers,
        plans,
        kinds: kinds_shared.borrow().clone(),
    })
}

fn lookup(scopes: &[Vec<(String, Scalar)>], name: &str) -> Option<Scalar> {
    for s in scopes.iter().rev() {
        for (n, k) in s.iter().rev() {
            if n == name {
                return Some(*k);
            }
        }
    }
    None
}

fn assign_scope(scopes: &[Vec<(String, Scalar)>], name: &str) -> Option<usize> {
    for (i, s) in scopes.iter().enumerate().rev() {
        if s.iter().any(|(n, _)| n == name) {
            return Some(i);
        }
    }
    None
}

/// Names a top-level body defines as local functions (closures, ch.24),
/// nested in ifs and loops included.
fn local_fn_names(stmts: &[sem::Stmt], out: &mut std::collections::HashSet<String>) {
    for s in stmts {
        match s {
            sem::Stmt::DefineLocalFn(f) => {
                out.insert(f.name.clone());
            }
            sem::Stmt::If { branches, other } => {
                for (_, b) in branches {
                    local_fn_names(b, out);
                }
                if let Some(ob) = other {
                    local_fn_names(ob, out);
                }
            }
            sem::Stmt::RepeatTimes { body, .. }
            | sem::Stmt::RepeatForever { body }
            | sem::Stmt::RepeatWhile { body, .. }
            | sem::Stmt::ForRange { body, .. }
            | sem::Stmt::ForIn { body, .. } => local_fn_names(body, out),
            _ => {}
        }
    }
}

fn scan_stmts(
    prog: &sem::Program,
    stmts: &[sem::Stmt],
    scopes: &mut Vec<Vec<(String, Scalar)>>,
    in_fn: bool,
    fx: &mut Fx,
) -> Result<(), String> {
    for st in stmts {
        scan_stmt(prog, st, scopes, in_fn, fx)?;
    }
    Ok(())
}

fn scan_stmt(
    prog: &sem::Program,
    st: &sem::Stmt,
    scopes: &mut Vec<Vec<(String, Scalar)>>,
    in_fn: bool,
    fx: &mut Fx,
) -> Result<(), String> {
    match st {
        sem::Stmt::Note => Ok(()),
        sem::Stmt::DefineLocalFn(f) => {
            // A local function (closure, ch.24) lowers like a top-level
            // function: its body is machine-compiled, and every free name
            // it reads becomes a capture value passed by the caller (the
            // interpreter's DefineLocalFn snapshot + shared borrow).
            if f.is_generator
                || f.can_fail
                || !f.requires.is_empty()
                || !f.ensures.is_empty()
                || f.default_last.is_some()
            {
                return Err(format!("the local function '{}' uses a feature the scalar backend does not lower in M3", f.name));
            }
            // the closure's own scope starts from its stated inputs; free
            // reads become captures (kind from the name's sem type)
            let mut scopes2: Vec<Vec<(String, Scalar)>> = vec![Vec::new()];
            for (j, t) in f.input_types.iter().enumerate() {
                let Some(sem::ParamType::K(kind)) = t else {
                    return Err(format!("the local function '{}' takes an input with no stated kind (M3-S9: it runs through the evaluator in M3)", f.name));
                };
                let Some(s) = kind_scalar(kind) else {
                    return Err(format!("the local function '{}' takes a kind the scalar backend does not lower in M3", f.name));
                };
                scopes2[0].push((f.inputs[j].0.clone(), s));
            }
            // the closure's free reads resolve against the defining walk:
            // flatten the walk's scopes with the outermost scope LAST
            // (lookup order preserved — innermost binding wins)
            let mut flat: Vec<(String, Scalar)> = Vec::new();
            for s in scopes.iter().rev() {
                for (n, k) in s.iter().rev() {
                    flat.push((n.clone(), *k));
                }
            }
            let mut fx2 = Fx::for_closure(fx, flat);
            let ret = match &f.body {
                sem::FnBody::Block(body) => {
                    if !always_gives(body) {
                        return Err(format!(
                        "the local function '{}' does not give back on every path; the evaluator runs it in M3",
                        f.name
                    ));
                    }
                    scan_stmts(prog, body, &mut scopes2, true, &mut fx2)?;
                    fn_result_scalar(f).ok_or_else(|| {
                        format!("the local function '{}' does not state one result kind (M3-S9: it runs through the evaluator in M3)", f.name)
                    })?
                }
                // one-line closure: the kind comes from the expression
                // itself (the closure scan records its free reads as caps)
                sem::FnBody::Expr(e) => scan_expr(prog, e, &scopes2, &fx2)
                    .map_err(|err| format!("the local function '{}': {err}", f.name))?,
            };
            // the snapshot: every free name the body read, resolved here
            // against the walk that defines the closure (order and kinds of
            // the interpreter's DefineLocalFn capture list)
            let mut caps: Vec<(String, Scalar)> = Vec::new();
            for (n, _) in fx2.caps.borrow().iter() {
                let k = lookup(scopes, n).ok_or_else(|| {
                    format!(
                        "the local function '{}' reads the name '{n}' that its definition does not see; the evaluator runs it in M3",
                        f.name
                    )
                })?;
                caps.push((n.clone(), k));
            }
            // nested closure plans (a To inside this closure's body) were
            // registered during the body scan in the shared plan list; this
            // closure must be first, so callers resolve it directly
            fx.plans.borrow_mut().push(CFnPlan { name: f.name.clone(), def: f.clone(), caps, ret });
            // callable from here on, in this walk (interp: the name binds
            // to a closure value when the sentence runs)
            fx.kinds.borrow_mut().insert(f.name.clone(), ret);
            fx.fns.insert(f.name.clone());
            Ok(())
        }
        sem::Stmt::Define(d) => {
            if d.fallback.is_some() {
                return Err("a definition with 'If that fails use...' runs through the evaluator in M3".into());
            }
            let k = scan_expr(prog, &d.expr, scopes, fx)?;
            scopes.last_mut().unwrap().push((d.name.clone(), k));
            Ok(())
        }
        sem::Stmt::Define(d) => {
            if d.fallback.is_some() {
                return Err("a definition with 'If that fails use...' runs through the evaluator in M3".into());
            }
            let k = scan_expr(prog, &d.expr, scopes, fx)?;
            scopes.last_mut().unwrap().push((d.name.clone(), k));
            Ok(())
        }
        sem::Stmt::Set { name, expr } => {
            let k = scan_expr(prog, expr, scopes, fx)?;
            match assign_scope(scopes, name) {
                Some(i) => {
                    scopes[i].retain(|(n, _)| n != name);
                    scopes[i].push((name.clone(), k));
                    Ok(())
                }
                None => {
                    // Frame.assign defines into the last scope when the name
                    // is unset, at top level and inside functions alike.
                    scopes.last_mut().unwrap().push((name.clone(), k));
                    Ok(())
                }
            }
        }
        sem::Stmt::Say { expr, mods, lines } => {
            if mods.width.is_some() {
                return Err("a Say with a width phrase runs through the evaluator in M3".into());
            }
            if !lines.is_empty() {
                if matches!(&expr.e, E::Flat(v) if v.is_empty()) {
                    return Ok(()); // only literal lines
                }
                return Err("a Say whose lines join a value runs through the evaluator in M3".into());
            }
            match &expr.e {
                E::Word(_) => Ok(()),
                E::Flat(pieces) => {
                    // interp.rs: every piece is shown (its own kind), the
                    // shown texts join with one space, then a newline (or
                    // not, for Say without). Words are pool texts; every
                    // other piece must scan to a scalar.
                    for p in pieces {
                        if matches!(&p.e, E::Word(_)) {
                            continue;
                        }
                        scan_expr(prog, p, scopes, fx).map(|_| ())?;
                    }
                    Ok(())
                }
                _ => {
                    let k = scan_expr(prog, expr, scopes, fx)?;
                    if mods.places.is_some() && k != Scalar::Decimal {
                        return Err("a Say with a places phrase must give decimals in M3".into());
                    }
                    Ok(())
                }
            }
        }
        sem::Stmt::Ask { .. } => Err("an Ask sentence runs through the evaluator in M3".into()),
        sem::Stmt::If { branches, other } => {
            for (cond, body) in branches {
                let k = scan_expr(prog, cond, scopes, fx)?;
                if k != Scalar::Boolean {
                    return Err("an If condition must give yes or no in M3's scalar backend".into());
                }
                scopes.push(Vec::new());
                let r = scan_stmts(prog, body, scopes, in_fn, fx);
                scopes.pop();
                r?;
            }
            if let Some(ob) = other {
                scopes.push(Vec::new());
                let r = scan_stmts(prog, ob, scopes, in_fn, fx);
                scopes.pop();
                r?;
            }
            Ok(())
        }
        sem::Stmt::RepeatTimes { count, body } => {
            scan_expr(prog, count, scopes, fx)?;
            scopes.push(Vec::new());
            let r = scan_stmts(prog, body, scopes, in_fn, fx);
            scopes.pop();
            r
        }
        sem::Stmt::RepeatForever { body } => {
            scopes.push(Vec::new());
            let r = scan_stmts(prog, body, scopes, in_fn, fx);
            scopes.pop();
            r
        }
        sem::Stmt::RepeatWhile { cond, body } => {
            let k = scan_expr(prog, cond, scopes, fx)?;
            if k != Scalar::Boolean {
                return Err("a Repeat while condition must give yes or no in M3's scalar backend".into());
            }
            scopes.push(Vec::new());
            let r = scan_stmts(prog, body, scopes, in_fn, fx);
            scopes.pop();
            r
        }
        sem::Stmt::ForRange { var, from, to, body } => {
            let fk = scan_expr(prog, from, scopes, fx)?;
            let _ = fk;
            let tk = scan_expr(prog, to, scopes, fx)?;
            let _ = tk;
            // the loop variable reads as a whole number on every pass:
            // interp.rs runs both bounds through as_i64 (decimals round)
            scopes.push(vec![(var.clone(), Scalar::Whole)]);
            let r = scan_stmts(prog, body, scopes, in_fn, fx);
            scopes.pop();
            r
        }
        sem::Stmt::GiveBack(v) => {
            match v {
                Some(e) => { scan_expr(prog, e, scopes, fx).map(|_| ())?; }
                None => {
                    return Err("Give back with no value gives one missing value; the evaluator handles it".into());
                }
            }
            Ok(())
        }
        sem::Stmt::Stop | sem::Stmt::Skip => Ok(()),
        // M4 (Appendix K): task, together, wait, sleep and stop-task
        // sentences run through the embedded evaluator for now (the eager
        // first cut keeps their bodies whole on the interpreter side);
        // the classify gate is all-or-nothing, so a program holding one
        // of these is 100% evaluator.
        sem::Stmt::StartTask { .. } | sem::Stmt::WaitFor { .. }
        | sem::Stmt::DoTogether { .. } | sem::Stmt::StopTask { .. }
        | sem::Stmt::SleepFor { .. } => Err("a task or pause sentence runs through the evaluator in M4 (the worker pool is a later increment)".into()),
        // M4 (Appendix K): channel/guarded/atomic sentences hold shared
        // state the native lowering does not model yet; any program with
        // one is 100% evaluator in this cut (same all-or-nothing gate).
        sem::Stmt::Send { .. } | sem::Stmt::Receive { .. } | sem::Stmt::AtomicAdd { .. } => {
            Err("a channel, guarded, atomic or counter sentence runs through the evaluator in M4 (native shared-state lowering is a later increment)".into())
        }
        // M4-4 (Appendix K 7.3/7.4): timers, stream loops, worker counts
        // and spreads appear in no sentence list above and land here:
        // a program holding one is 100% evaluator (same all-or-nothing
        // gate; the rounds run through the interpreter).
        sem::Stmt::AfterTimer { .. } | sem::Stmt::EveryTimer { .. }
        | sem::Stmt::StreamLoop { .. } | sem::Stmt::UseWorkers { .. }
        | sem::Stmt::Spread { .. } => {
            Err("a timer, stream-loop or spread sentence runs through the evaluator in M4 (native single-pass scheduling is a later increment)".into())
        }
        // M4-5 (Appendix K 7.5): every file sentence touches the disk at
        // run time; a program holding one is 100% evaluator (same gate;
        // native disk access is a later increment).
        sem::Stmt::ReadFile { .. } | sem::Stmt::ReadBytes { .. }
        | sem::Stmt::WriteFile { .. } | sem::Stmt::AppendFile { .. }
        | sem::Stmt::ReplaceFile { .. } | sem::Stmt::ForEachLine { .. }
        | sem::Stmt::MakeFolder { .. } | sem::Stmt::RemovePath { .. }
        | sem::Stmt::MovePath { .. } | sem::Stmt::DuplicatePath { .. }
        | sem::Stmt::ListFolder { .. } | sem::Stmt::MakeTempFile { .. }
        | sem::Stmt::WhenFileChanges { .. } | sem::Stmt::ZipOp { .. }
        // M4-6 (Appendix K 7.6): the format sentences decode/encode typed
        // shapes at run time (same all-or-nothing gate)
        | sem::Stmt::ReadFormat { .. } | sem::Stmt::ReadFormatText { .. }
        | sem::Stmt::SaveFormat { .. } => {
            Err("a file sentence runs through the evaluator in M4 (native disk access is a later increment)".into())
        }
        // M4-7 (Appendix K 7.7): Use seed changes the evaluator's random
        // generator; it has no native form (same all-or-nothing gate)
        | sem::Stmt::UseSeed { .. } => {
            Err("a seed sentence runs through the evaluator in M4 (the seed state is an evaluator detail)".into())
        }
        // M4-8 (Appendix K 7.10/7.11): Run starts another program, Exit ends
        // the process, the signal block is a task and the input loop
        // streams - all run through the embedded evaluator (same
        // all-or-nothing gate; the Takes/Option seeding also lives there)
        sem::Stmt::RunProc { .. } | sem::Stmt::Exit { .. }
        | sem::Stmt::WhenSignal { .. } | sem::Stmt::ForEachInput { .. }
        // M4-9 (7.12): Log and Use log level touch the run's error stream
        // and log level - they run through the embedded evaluator too
        | sem::Stmt::Log { .. } | sem::Stmt::LogLevel { .. }
        // M4-10 (7.8): the network sentences block on sockets and keep
        // handler contexts in the evaluator - no native form in M4
        | sem::Stmt::Fetch { .. } | sem::Stmt::PostTo { .. }
        | sem::Stmt::Serve { .. } | sem::Stmt::WhenSomeone { .. }
        | sem::Stmt::WhenLive { .. } | sem::Stmt::Respond { .. }
        | sem::Stmt::PageDecl { .. } | sem::Stmt::WsSend { .. }
        | sem::Stmt::WsRecv { .. } | sem::Stmt::Careful { .. } => {
            Err("a system or tool sentence runs through the evaluator in M4 (native process and signal handling is a later increment)".into())
        }
        other => Err(format!(
            "'{}' runs through the evaluator in M3 (M3 lowers control flow and number words; later milestones lower the rest)",
            long_word(other),
        )),
    }
}

fn long_word(st: &sem::Stmt) -> &'static str {
    match st {
        sem::Stmt::ForIn { .. } => "For each",
        sem::Stmt::Evaluate { .. } => "Apply/Combine",
        sem::Stmt::Append { .. } => "Add ... to",
        sem::Stmt::Put { .. } => "Put",
        sem::Stmt::Remove { .. } => "Remove",
        sem::Stmt::RemoveFirst { .. } => "Remove first",
        sem::Stmt::SetPart { .. } => "Set ... of",
        sem::Stmt::LookAt { .. } => "Look at",
        sem::Stmt::DefineEnum { .. } => "is ... or",
        sem::Stmt::Try { .. } => "Try",
        sem::Stmt::Fail { .. } => "Fail with",
        sem::Stmt::PassFailureUp => "Pass failure up",
        sem::Stmt::Close { .. } => "Close",
        sem::Stmt::Share { .. } => "Share",
        sem::Stmt::Use { .. } => "Use",
        sem::Stmt::Test { .. } => "Test",
        sem::Stmt::Check { .. } => "Check",
        sem::Stmt::Pretend { .. } => "Pretend",
        sem::Stmt::HandBack(_) => "Hand back",
        sem::Stmt::DefineLocalFn(_) => "a local To",
        _ => "that sentence",
    }
}

fn scan_expr(
    prog: &sem::Program,
    e: &Expr,
    scopes: &[Vec<(String, Scalar)>],
    fx: &Fx,
) -> Result<Scalar, String> {
    match &e.e {
        E::Whole(_) | E::Dec(_) | E::Boolean(_) => kind_scalar(&e.kind)
            .ok_or_else(|| "a literal of a kind the scalar backend does not lower".to_string()),
        E::Name(n) => {
            if let Some(k) = lookup(scopes, n) {
                return Ok(k);
            }
            // a free read inside a closure body records a capture: the kind
            // comes from the defining walk's binding of the name (the inter-
            // preter's DefineLocalFn snapshot resolves captures the same way)
            if fx.allow_caps {
                if !fx.caps.borrow().contains_key(n.as_str()) {
                    fx.caps.borrow_mut().insert(n.clone(), ());
                }
                return fx
                    .cap_kinds
                    .iter()
                    .find(|(cn, _)| cn == n)
                    .map(|(_, k)| *k)
                    .ok_or_else(|| {
                        format!("the name '{n}' is read where it is not defined; the evaluator handles it")
                    });
            }
            Err(format!("the name '{n}' is read where it may not be defined yet; the evaluator handles it"))
        }
        E::Neg(inner) => {
            let v = scan_expr(prog, inner, scopes, fx)?;
            match v {
                Scalar::Whole | Scalar::Decimal => Ok(v),
                _ => Err("minus on yes-or-no runs through the evaluator".into()),
            }
        }
        E::Binary { op, l, r } => {
            let a = scan_expr(prog, l, scopes, fx)?;
            let b = scan_expr(prog, r, scopes, fx)?;
            bin_scalar(*op, a, b)
                .ok_or_else(|| format!("the words '{}' on those kinds run through the evaluator in M3", op_word(*op)))
        }
        E::DivWhole(l, r) => {
            let a = scan_expr(prog, l, scopes, fx)?;
            let b = scan_expr(prog, r, scopes, fx)?;
            if a != Scalar::Whole || b != Scalar::Whole {
                return Err("whole divided by on decimals runs through the evaluator in M3".into());
            }
            Ok(Scalar::Whole)
        }
        E::Rem(l, r) => {
            let a = scan_expr(prog, l, scopes, fx)?;
            let b = scan_expr(prog, r, scopes, fx)?;
            if a != Scalar::Whole || b != Scalar::Whole {
                return Err("a remainder of decimals runs through the evaluator in M3".into());
            }
            Ok(Scalar::Whole)
        }
        E::Pow(l, r) => {
            // the interpreter runs both sides through as_i64 (decimals round,
            // booleans are 0/1), and the result is whole
            scan_expr(prog, l, scopes, fx)?;
            scan_expr(prog, r, scopes, fx)?;
            Ok(Scalar::Whole)
        }
        E::Round(inner, _) => {
            let k = scan_expr(prog, inner, scopes, fx)?;
            match k {
                Scalar::Whole | Scalar::Decimal => Ok(Scalar::Whole),
                Scalar::Boolean => Err("the nearest-to word on yes-or-no runs through the evaluator in M3".to_string()),
            }
        }
        E::AsWhole(inner) => {
            // interp.rs: a whole stays whole; a decimal conversion can fail
            let k = scan_expr(prog, inner, scopes, fx)?;
            match k {
                Scalar::Whole => Ok(Scalar::Whole),
                Scalar::Decimal => {
                    Err("as whole number on a decimal can fail; the evaluator runs it in M3".into())
                }
                Scalar::Boolean => {
                    Err("as whole number on yes-or-no runs through the evaluator in M3".into())
                }
            }
        }
        E::AsDecimal(inner) => {
            // interp.rs: whole -> as f64 (never fails), decimal passes through
            let k = scan_expr(prog, inner, scopes, fx)?;
            match k {
                Scalar::Whole | Scalar::Decimal => Ok(Scalar::Decimal),
                Scalar::Boolean => {
                    Err("as decimal on yes-or-no runs through the evaluator in M3".into())
                }
            }
        }
        E::AndOr(l, r, is_and) => {
            let a = scan_expr(prog, l, scopes, fx)?;
            let b = scan_expr(prog, r, scopes, fx)?;
            if a == Scalar::Boolean && b == Scalar::Boolean {
                Ok(Scalar::Boolean)
            } else {
                Err(format!("'{}' on words that are not yes-or-no runs through the evaluator in M3", if *is_and { "and" } else { "or" }))
            }
        }
        E::Compare(c) => {
            let l = scan_expr(prog, &c.l, scopes, fx)?;
            let mut rs: Vec<Scalar> = Vec::new();
            for r in &c.r {
                rs.push(scan_expr(prog, r, scopes, fx)?);
            }
            compare_scalar(&c, l, rs.first().copied())
        }
        E::Call { name, args } => {
            if !fx.fns.contains(name.as_str()) {
                return Err(format!("'{name}' is a function the scalar backend does not lower in M3; the evaluator runs it"));
            }
            // interp.rs eval_call_values: a closure value of that name in
            // scope is called FIRST; a top-level function second. Mirror
            // that order here (a hoisted local exists in prog.funcs too).
            if let Some(plan) = fx.call_plan(prog, name) {
                if args.len() != plan.def.inputs.len() {
                    return Err(format!("the call to '{name}' gives the wrong input count"));
                }
                for (cn, ck) in &plan.caps {
                    match lookup(scopes, cn) {
                        Some(k) if k == *ck => {}
                        _ => {
                            return Err(format!(
                                "the call to the local function '{name}' is made where its captured name '{cn}' is not visible with the captured kind; the evaluator runs it"
                            ))
                        }
                    }
                }
                let mut got: Vec<Scalar> = Vec::new();
                for a in args {
                    got.push(scan_expr(prog, a, scopes, fx)?);
                }
                for (i, t) in plan.def.input_types.iter().enumerate() {
                    let want = match t {
                        Some(sem::ParamType::K(k)) => kind_scalar(k),
                        _ => None,
                    };
                    match (want, got.get(i)) {
                        (Some(w), Some(g)) if w == *g => {}
                        _ => return Err(format!("the kinds of the call to '{name}' run through the evaluator in M3")),
                    }
                }
                return Ok(plan.ret);
            }
            if let Some(f) = prog.funcs.iter().find(|f| f.name == *name) {
                if args.len() != f.inputs.len() {
                    return Err(format!("the call to '{name}' gives the wrong input count"));
                }
                let mut got: Vec<Scalar> = Vec::new();
                for a in args {
                    got.push(scan_expr(prog, a, scopes, fx)?);
                }
                for (i, t) in f.input_types.iter().enumerate() {
                    let want = match t {
                        Some(sem::ParamType::K(k)) => kind_scalar(k),
                        _ => None,
                    };
                    match (want, got.get(i)) {
                        (Some(w), Some(g)) if w == *g => {}
                        _ => return Err(format!("the kinds of the call to '{name}' run through the evaluator in M3")),
                    }
                }
                // stated kinds (block bodies) and kinds derived by earlier
                // scans (one-line bodies) both land in the shared map
                let k = fx
                    .kinds
                    .borrow()
                    .get(name.as_str())
                    .copied()
                    .or_else(|| fn_result_scalar(f));
                return k.ok_or_else(|| {
                    format!("the result kind of '{name}' runs through the evaluator in M3")
                });
            }
            // a call to a local function: its capture values must be visible
            // (with the captured kinds) in the walk that calls — the machine
            // call passes them, the interpreter takes them from its frame
            let plan = match fx.call_plan(prog, name) {
                Some(p) => p,
                None => {
                    return Err(format!(
                        "'{name}' is a function the scalar backend does not lower in M3; the evaluator runs it"
                    ))
                }
            };
            if args.len() != plan.def.inputs.len() {
                return Err(format!("the call to '{name}' gives the wrong input count"));
            }
            for (cn, ck) in &plan.caps {
                match lookup(scopes, cn) {
                    Some(k) if k == *ck => {}
                    _ => {
                        return Err(format!(
                        "the call to the local function '{name}' is made where its captured name '{cn}' is not visible with the captured kind; the evaluator runs it"
                    ))
                    }
                }
            }
            let mut got: Vec<Scalar> = Vec::new();
            for a in args {
                got.push(scan_expr(prog, a, scopes, fx)?);
            }
            for (i, t) in plan.def.input_types.iter().enumerate() {
                let want = match t {
                    Some(sem::ParamType::K(k)) => kind_scalar(k),
                    _ => None,
                };
                match (want, got.get(i)) {
                    (Some(w), Some(g)) if w == *g => {}
                    _ => return Err(format!("the kinds of the call to '{name}' run through the evaluator in M3")),
                }
            }
            Ok(plan.ret)
        }
        E::FileExists(_) => {
            // M4-G45: the disk read behind a file question is not lowered
            Err("a file question runs through the evaluator in M4 (native disk access is a later increment)".into())
        }
        E::JsonOf(_) => {
            // M4-6 (S46): the json encoding of an arbitrary value is not lowered
            Err("json of x runs through the evaluator in M4 (native json encoding is a later increment)".into())
        }
        // M4-7 (Appendix K 7.7): the time, random and secret reads run
        // through the embedded evaluator (same all-or-nothing gate)
        E::DateCtor { .. } | E::Today | E::Now | E::MomentAt { .. } | E::InZone { .. }
        | E::TimeShift { .. } | E::DurationOf { .. } | E::DaysBetween { .. }
        | E::SecondsBetween { .. } | E::RandomRange { .. } | E::RandomDec
        | E::RandomItem { .. } | E::Shuffled { .. } | E::HashOf(_) | E::SecretOf(_)
        | E::Reveal(_) => {
            Err("a time, random or secret read runs through the evaluator in M4 (native forms are a later increment)".into())
        }
        // M4-8 (Appendix K 7.10/7.11): the environment variable and the
        // standard-input reads are run-time reads of the outside world
        // (same gate)
        E::Environment { .. } | E::ReadInput => {
            Err("an environment or input read runs through the evaluator in M4 (native forms are a later increment)".into())
        }
        _ => Err("an expression of that shape runs through the evaluator in M3 (texts, lists, records and the like are lowered in later milestones)".into()),
    }
}

fn compare_scalar(c: &Comp, l: Scalar, r0: Option<Scalar>) -> Result<Scalar, String> {
    let r0 = r0.unwrap_or(Scalar::Whole);
    let ok_rel = matches!(
        c.rel,
        Rel::Equal | Rel::Not | Rel::Less | Rel::More | Rel::AtLeast | Rel::AtMost | Rel::Between
    );
    if !ok_rel {
        return Err("that comparison word runs through the evaluator in M3".into());
    }
    if c.rel == Rel::Equal || c.rel == Rel::Not {
        // cmp_eq has no (decimal, decimal) arm in the reference interpreter:
        // `is` on two decimals gives no. Keep the same answer. Both operands
        // still evaluate (they may print or fail), which the emitter does.
        if l == r0 {
            return Ok(Scalar::Boolean);
        }
        return Err("a comparison of two kinds the evaluator pairs differently runs through the evaluator in M3".into());
    }
    // ordering comparisons hold for whole and decimal in any mix (cmp_ord
    // converts through numeric)
    if l == Scalar::Boolean || r0 == Scalar::Boolean {
        return Err("a size comparison on yes-or-no runs through the evaluator in M3".into());
    }
    if c.rel == Rel::Between && c.r.len() != 2 {
        return Err("'is between' needs two values; the evaluator handles it".into());
    }
    Ok(Scalar::Boolean)
}

fn bin_scalar(op: Op, a: Scalar, b: Scalar) -> Option<Scalar> {
    use Op as O;
    if a == Scalar::Boolean || b == Scalar::Boolean {
        // bin_op pairs whole numbers with whole numbers and decimals with
        // decimals; with a yes-or-no in the mix the evaluator gives missing,
        // which register code does not represent
        return None;
    }
    let both_whole = a == Scalar::Whole && b == Scalar::Whole;
    match op {
        // the interpreter's exact promotion: whole/whole uses the checked
        // whole path; anything with a decimal in it runs bin_op's numeric
        // path (whole side converts) and gives a decimal
        O::Plus | O::Minus | O::Time => Some(if both_whole {
            Scalar::Whole
        } else {
            Scalar::Decimal
        }),
        O::DividedBy => Some(Scalar::Decimal),
        O::WrappingPlus
        | O::WrappingMinus
        | O::WrappingTimes
        | O::SaturatingPlus
        | O::SaturatingMinus
        | O::SaturatingTimes => {
            if both_whole {
                Some(Scalar::Whole)
            } else {
                None
            }
        }
        _ => None, // checked plus/minus/times can fail: the evaluator runs it
    }
}

fn op_word(op: Op) -> &'static str {
    match op {
        Op::Plus => "plus",
        Op::Minus => "minus",
        Op::Time => "times",
        Op::DividedBy => "divided by",
        Op::WholeDividedBy => "whole divided by",
        Op::CheckedPlus => "checked plus",
        Op::CheckedMinus => "checked minus",
        Op::CheckedTimes => "checked times",
        Op::WrappingPlus => "wrapping plus",
        Op::WrappingMinus => "wrapping minus",
        Op::WrappingTimes => "wrapping times",
        Op::SaturatingPlus => "saturating plus",
        Op::SaturatingMinus => "saturating minus",
        Op::SaturatingTimes => "saturating times",
        _ => "that word",
    }
}

// ================================================================ emission

/// how deep nested calls may go before T0607 (the interpreter's cap).
const MAX_DEPTH: i64 = 240;

/// The interpreter's fatal lines, exactly as `fatal()` formats them
/// (interp.rs: `Error: {cause} ({code})\nFix: {fix}`). The runtime prints
/// them with one trailing newline.
pub const T0603: &str =
    "Error: A whole number went past 64 bits. (T0603)\nFix: Use big number or checked plus.";
pub const T0604: &str =
    "Error: A whole number was divided by zero. (T0604)\nFix: Check the divisor.";
pub const T0607: &str = "Error: Calls nested too deep. (T0607)\nFix: Add a stop condition.";

/// Text pool: every literal the generated code prints, plus the error lines.
/// One shared data symbol, laid out in add order (deterministic, M3-S40).
struct Strings {
    bytes: Vec<u8>,
    map: std::collections::HashMap<String, u32>,
}

impl Strings {
    fn new() -> Self {
        Strings {
            bytes: Vec::new(),
            map: std::collections::HashMap::new(),
        }
    }
    fn add(&mut self, s: &str) -> (u32, u32) {
        if let Some(off) = self.map.get(s) {
            return (*off, s.len() as u32);
        }
        let off = self.bytes.len() as u32;
        self.bytes.extend_from_slice(s.as_bytes());
        self.map.insert(s.to_string(), off);
        (off, s.len() as u32)
    }
}

/// The runtime functions generated code may call (declared Import, resolved
/// at link time against liblykaon_rt).
const RT_MAIN: &str = "lykaon_rt_main";
const RT_FLUSH: &str = "lykaon_rt_flush";
const RT_FAIL: &str = "lykaon_rt_fail";
const RT_SAY_WHOLE: &str = "lykaon_rt_say_whole";
const RT_SAY_DEC: &str = "lykaon_rt_say_dec";
const RT_SAY_BOOL: &str = "lykaon_rt_say_bool";
const RT_SAY_TEXT: &str = "lykaon_rt_say_text";
const RT_MUL: &str = "lykaon_rt_mul_whole";
const RT_NEG: &str = "lykaon_rt_neg_whole";
const RT_POW: &str = "lykaon_rt_pow_whole";
const RT_ROUND: &str = "lykaon_rt_round_dec"; // (f64 bits, even) -> i64
const RT_WRAP: &str = "lykaon_rt_wrap_whole"; // (op, a, b) -> i64
const RT_DIVI: &str = "lykaon_rt_whole_divided_by";
const RT_REM: &str = "lykaon_rt_whole_rem";

/// op codes for lykaon_rt_wrap_whole (whole math words that cannot fail: the
/// wrapping and saturating families, ch.19).
const WADD: i64 = 0;
const WSUB: i64 = 1;
const WMUL: i64 = 2;
const SADD: i64 = 3;
const SSUB: i64 = 4;
const SMUL: i64 = 5;

/// What generated code can abort on (one shared rt_fail call with the
/// interpreter's exact fatal line).
#[derive(Clone, Copy)]
enum Fail {
    Over,    // T0603
    DivZero, // T0604
    Deep,    // T0607
}

/// One branch argument for jump/brif: 0.125's branch argument lists take
/// `&BlockArg` references (BlockArg::Value wraps the value to pass).
fn bar1(v: ir::Value) -> [ir::BlockArg; 1] {
    [ir::BlockArg::Value(v)]
}

pub struct Codegen {
    module: ObjectModule,
    conv: CallConv,
    strings: Strings,
    /// the string pool's data symbol; None until the Full path declares it
    pool: Option<DataId>,
    user_fns: std::collections::HashMap<String, FuncId>,
    rt_fns: std::collections::HashMap<&'static str, FuncId>,
    /// the machine plans of the local functions (closures, ch.24): indexed
    /// by the same order the symbols were declared (lykaon_clo_N)
    clo_plans: Vec<CFnPlan>,
    /// result kinds the scan learned (stated or derived); the emitter's
    /// kind queries resolve call results through this map
    fn_kinds: std::collections::BTreeMap<String, Scalar>,
    /// pool offsets of the three fatal lines (T0603, T0604, T0607)
    errs: [(u32, u32); 3],
}

/// One SSA variable binding: a name visible in a scope, its register type,
/// and the interpreter-equivalent lookup chain of scopes that carries it.
#[derive(Clone, Copy)]
struct Bind {
    var: Variable,
    kind: Scalar,
}

/// Where Stop. and Skip. must jump for the innermost loop (interp.rs breaks
/// or continues the innermost one).
#[derive(Clone, Copy)]
struct LoopT {
    exit: ir::Block, // Stop target
    next: ir::Block, // Skip target
    /// the value the loop's counter block expects at a Skip (its current
    /// value): None when the next block takes no parameter
    carry: Option<ir::Value>,
}

/// Compile-time state of one walk (a function body or the top-level body).
/// Scopes mirror the interpreter's frame stack; `depth` holds the hidden
/// depth parameter in lowered functions (None in the top-level body, which
/// the interpreter runs at depth 0).
struct Walk {
    gv: ir::GlobalValue,
    scopes: Vec<Vec<(String, Bind)>>,
    loops: Vec<LoopT>,
    depth: Option<Variable>,
    /// capture snapshots: the values a local function saw when its `To`
    /// sentence ran (interp.rs DefineLocalFn). Closure name -> captured
    /// name -> snapshot register. Call sites read these, not live values.
    snaps: std::collections::HashMap<String, Vec<(String, Variable)>>,
    is_fn: bool,
    end_block: ir::Block,
    ended: bool, // the current block already ends (Give back / Stop / Skip)
}

impl Codegen {
    pub fn new() -> Result<Self, String> {
        let isa_builder = native_builder().map_err(|e| format!("native builder: {e}"))?;
        let flags = settings::Flags::new(settings::builder());
        let isa: cranelift_codegen::isa::OwnedTargetIsa = isa_builder
            .finish(flags)
            .map_err(|e| format!("isa finish: {e}"))?;
        let backend = ObjectBuilder::new(
            isa,
            b"lykaon".to_vec(),
            Box::new(cranelift_module::default_libcall_names()),
        )
        .map_err(|e| format!("object builder: {e}"))?;
        // Microsoft x64 convention on Windows, System V on Linux (M3, section 9).
        let conv = if cfg!(windows) {
            CallConv::WindowsFastcall
        } else {
            CallConv::SystemV
        };
        Ok(Codegen {
            module: ObjectModule::new(backend),
            conv,
            strings: Strings::new(),
            pool: None,
            user_fns: std::collections::HashMap::new(),
            rt_fns: std::collections::HashMap::new(),
            clo_plans: Vec::new(),
            fn_kinds: std::collections::BTreeMap::new(),
            errs: [(0, 0); 3],
        })
    }

    /// Produce the object file for one program.
    pub fn build_object(
        source: &str,
        prog: &sem::Program,
        mode: &str,
    ) -> Result<(Vec<u8>, LowerKind), String> {
        let mut cg = Codegen::new()?;
        let mode = BuildMode::from_str(mode);
        let kind = classify(prog);
        match &kind {
            LowerKind::Full => cg.compile_full(prog)?,
            LowerKind::Embedded { .. } => cg.compile_embedded(source, mode)?,
        }
        cg.finish_module()?;
        let product = cg.module.finish();
        let bytes = product.object.write().map_err(|e| format!("emit: {e}"))?;
        Ok((bytes, kind))
    }

    /// Define the string pool once all functions have added their texts.
    fn finish_module(&mut self) -> Result<(), String> {
        let Some(id) = self.pool else { return Ok(()) };
        let bytes = std::mem::take(&mut self.strings.bytes);
        let mut desc = cranelift_module::DataDescription::new();
        desc.define(bytes.into_boxed_slice());
        self.module
            .define_data(id, &desc)
            .map_err(|e| format!("define data: {e}"))
    }

    fn fn_sig(&self, n_params: usize, ret: Option<ir::Type>) -> Signature {
        self.sig_from(vec![WORD; n_params], ret)
    }

    fn sig_from(&self, mut params: Vec<ir::Type>, ret: Option<ir::Type>) -> Signature {
        let mut sig = Signature::new(self.conv);
        for p in params.drain(..) {
            sig.params.push(ir::AbiParam::new(p));
        }
        if let Some(t) = ret {
            sig.returns.push(ir::AbiParam::new(t));
        }
        sig
    }

    // ---------------------------------------------------------- embedded

    /// Object whose `lykaon_main` runs the embedded source through liblykaon_rt's
    /// embedded evaluator (byte-exact with `lykaon run` by construction).
    fn compile_embedded(&mut self, source: &str, mode: BuildMode) -> Result<(), String> {
        let mut desc = cranelift_module::DataDescription::new();
        desc.define(source.as_bytes().to_vec().into_boxed_slice());
        let data_id = self
            .module
            .declare_data("lykaon_src", Linkage::Local, false, false)
            .map_err(|e| format!("{e:?}"))?;
        self.module
            .define_data(data_id, &desc)
            .map_err(|e| format!("{e:?}"))?;

        let sig = self.sig_from(vec![WORD, WORD, WORD], Some(RET));
        let fid = self
            .module
            .declare_function("lykaon_main", Linkage::Export, &sig)
            .map_err(|e| format!("{e:?}"))?;
        let mut ctx = Context::new();
        ctx.func = Function::with_name_signature(UserFuncName::user(0, fid.as_u32()), sig);
        let mut fctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let rt_main = self.declare_rt(&mut builder.func, RT_MAIN, &[WORD, WORD, WORD], Some(WORD));
        let gv = self.module.declare_data_in_func(data_id, &mut builder.func);
        let ptr = builder.ins().global_value(WORD, gv);
        let len = builder.ins().iconst(WORD, source.len() as i64);
        let mode_v = builder.ins().iconst(WORD, mode.code());
        let call = builder.ins().call(rt_main, &[ptr, len, mode_v]);
        let code = builder.func.dfg.inst_results(call)[0];
        let m = builder.ins().ireduce(RET, code);
        builder.ins().return_(&[m]);
        builder.seal_all_blocks();
        builder.finalize();
        self.module
            .define_function(fid, &mut ctx)
            .map_err(|e| format!("{e:?}"))?;
        Ok(())
    }

    // -------------------------------------------------------------- full

    fn compile_full(&mut self, prog: &sem::Program) -> Result<(), String> {
        // Stage 1: every function must be scalar-shaped, or embedded. The
        // scan also collects the machine plans of the local functions
        // (closures, ch.24) defined in the top-level body and the result
        // kind of every callable (stated, or derived for one-line bodies).
        let scan = scan_program(prog)?;
        if std::env::var_os("Lykaon_DEBUG_SCAN").is_some() {
            eprintln!(
                "funcs=[{:?}]",
                prog.funcs
                    .iter()
                    .map(|f| f.name.clone())
                    .collect::<Vec<_>>()
            );
            eprintln!(
                "lower={:?}",
                scan.lowers
                    .iter()
                    .map(|(i, k)| (format!("{}[{}]", prog.funcs[*i].name, i), format!("{k:?}")))
                    .collect::<Vec<_>>()
            );
            eprintln!(
                "plans={}",
                scan.plans
                    .iter()
                    .map(|p| format!("{}(caps={:?},ret={:?})", p.name, p.caps, p.ret))
                    .collect::<Vec<_>>()
                    .join("; ")
            );
            eprintln!("kinds={:?}", scan.kinds);
        }
        self.fn_kinds = scan.kinds.clone();
        let lowers = &scan.lowers;

        // declare every function symbol first (calls may reference any of
        // them): top-level functions, then the closures (capture params
        // first, then inputs, then depth — the interpreter's frame order)
        self.user_fns.clear();
        for (i, k) in lowers {
            let f = &prog.funcs[*i];
            let mut ptys: Vec<ir::Type> = Vec::new();
            for t in f.input_types.iter() {
                let Some(sem::ParamType::K(kind)) = t else {
                    unreachable!()
                };
                ptys.push(kind_scalar(kind).unwrap().ty());
            }
            ptys.push(WORD); // hidden depth parameter (T0607)
            let sig = self.sig_from(ptys, Some(k.ty()));
            let fid = self
                .module
                .declare_function(&format!("lykaon_fn_{}", i), Linkage::Export, &sig)
                .map_err(|e| format!("{e:?}"))?;
            self.user_fns.insert(f.name.clone(), fid);
        }
        self.clo_plans = scan.plans.clone();
        for (c, plan) in scan.plans.iter().enumerate() {
            let mut ptys: Vec<ir::Type> = plan.caps.iter().map(|(_, k)| k.ty()).collect();
            for t in plan.def.input_types.iter() {
                let Some(sem::ParamType::K(kind)) = t else {
                    unreachable!()
                };
                ptys.push(kind_scalar(kind).unwrap().ty());
            }
            ptys.push(WORD); // hidden depth parameter (T0607)
            let sig = self.sig_from(ptys, Some(plan.ret.ty()));
            let fid = self
                .module
                .declare_function(&format!("lykaon_clo_{}", c), Linkage::Export, &sig)
                .map_err(|e| format!("{e:?}"))?;
            self.user_fns.insert(plan.name.clone(), fid);
        }
        let main_sig = self.fn_sig(0, Some(RET));
        let main_id = self
            .module
            .declare_function("lykaon_main", Linkage::Export, &main_sig)
            .map_err(|e| format!("{e:?}"))?;

        // the pool symbol and the three constant fatal lines; they are added
        // first, so their offsets never move (later texts extend the pool)
        let pool = self
            .module
            .declare_data("lykaon_strings", Linkage::Local, false, false)
            .map_err(|e| format!("{e:?}"))?;
        self.pool = Some(pool);
        let (o603, l603) = self.strings.add(T0603);
        let (o604, l604) = self.strings.add(T0604);
        let (o607, l607) = self.strings.add(T0607);
        self.errs = [(o603, l603), (o604, l604), (o607, l607)];

        // compile each function, then the top-level main, then the closures
        for (i, k) in lowers.clone() {
            self.compile_function(prog, i, k)?;
        }
        self.compile_main(prog, main_id)?;
        for (c, plan) in scan.plans.iter().enumerate() {
            self.compile_closure(prog, plan, c)?;
        }
        Ok(())
    }

    fn compile_function(
        &mut self,
        prog: &sem::Program,
        idx: usize,
        ret: Scalar,
    ) -> Result<(), String> {
        let fname = prog.funcs[idx].name.clone();
        let n_inputs = prog.funcs[idx].inputs.len();
        let mut ptys: Vec<ir::Type> = Vec::new();
        for t in prog.funcs[idx].input_types.iter() {
            let Some(sem::ParamType::K(kind)) = t else {
                unreachable!()
            };
            ptys.push(kind_scalar(kind).unwrap().ty());
        }
        ptys.push(WORD); // hidden depth parameter (T0607)
        let sig = self.sig_from(ptys, Some(ret.ty()));
        let fid = self.user_fns[&fname];

        let mut ctx = Context::new();
        ctx.func = Function::with_name_signature(UserFuncName::user(0, self.call_id(idx)), sig);
        let mut fctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        let gv = self
            .module
            .declare_data_in_func(self.pool.unwrap(), &mut builder.func);
        let end = builder.create_block();
        let params: Vec<ir::Value> = builder.block_params(entry).to_vec();
        builder.switch_to_block(entry);

        let mut w = Walk {
            gv,
            scopes: vec![Vec::new()],
            loops: vec![LoopT {
                exit: end,
                next: end,
                carry: None,
            }],
            depth: None,
            snaps: std::collections::HashMap::new(),
            is_fn: true,
            end_block: end,
            ended: false,
        };
        // seed the call scope with the inputs, then the depth parameter
        // (interp.rs starts every call frame from its inputs)
        for (j, t) in prog.funcs[idx].input_types.iter().enumerate() {
            let Some(sem::ParamType::K(kind)) = t else {
                unreachable!()
            };
            let s = kind_scalar(kind).unwrap();
            let var = builder.declare_var(s.ty());
            builder.def_var(var, params[j]);
            let name = prog.funcs[idx].inputs[j].0.clone();
            w.scopes[0].push((name, Bind { var, kind: s }));
        }
        let dvar = builder.declare_var(WORD);
        builder.def_var(dvar, params[n_inputs]);
        w.depth = Some(dvar);

        let stmts: Option<&[sem::Stmt]> = match &prog.funcs[idx].body {
            sem::FnBody::Block(s) => Some(s),
            // one-line `give <expr>`: emit the expression, hand it back
            sem::FnBody::Expr(e) => {
                let v = self.eval_expr(prog, &mut builder, &mut w, e)?;
                builder.ins().return_(&[v]);
                w.ended = true;
                None
            }
        };
        if let Some(stmts) = stmts {
            self.walk_stmts(prog, &mut builder, &mut w, stmts)?;
        }
        if !w.ended {
            // unreachable in a scanned program (the evaluator would give
            // `missing`, which the scanner never accepts); return the kind's
            // zero defensively so the machine function always terminates
            let z = match ret {
                Scalar::Whole => builder.ins().iconst(WORD, 0),
                Scalar::Boolean => builder.ins().iconst(BOOL, 0),
                Scalar::Decimal => builder.ins().f64const(Ieee64::with_float(0.0)),
            };
            builder.ins().return_(&[z]);
        }
        builder.seal_all_blocks();
        builder.finalize();
        if std::env::var_os("Lykaon_IR").is_some() {
            eprintln!(
                "=== IR of '{}'\n{}",
                prog.funcs[idx].name,
                ctx.func.display()
            );
        }
        self.module
            .define_function(fid, &mut ctx)
            .map_err(|e| format!("compiling '{}': {e:?}", prog.funcs[idx].name))?;
        Ok(())
    }

    fn call_id(&self, idx: usize) -> u32 {
        (0x1000 + idx as u32 * 2) as u32
    }

    /// Compile one local function (closure, ch.24): capture values first,
    /// then inputs, then the hidden depth parameter — the interpreter's
    /// frame order (eval_closure seeds captures, then overrides with
    /// inputs).
    fn compile_closure(
        &mut self,
        prog: &sem::Program,
        plan: &CFnPlan,
        idx: usize,
    ) -> Result<(), String> {
        let mut ptys: Vec<ir::Type> = plan.caps.iter().map(|(_, k)| k.ty()).collect();
        for t in plan.def.input_types.iter() {
            let Some(sem::ParamType::K(kind)) = t else {
                unreachable!()
            };
            ptys.push(kind_scalar(kind).unwrap().ty());
        }
        ptys.push(WORD); // hidden depth parameter (T0607)
        let sig = self.sig_from(ptys, Some(plan.ret.ty()));
        let fid = self.user_fns[&plan.name];

        let mut ctx = Context::new();
        ctx.func =
            Function::with_name_signature(UserFuncName::user(0, 0x2000 + idx as u32 * 2), sig);
        let mut fctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        let gv = self
            .module
            .declare_data_in_func(self.pool.unwrap(), &mut builder.func);
        let end = builder.create_block();
        let params: Vec<ir::Value> = builder.block_params(entry).to_vec();
        builder.switch_to_block(entry);

        let mut w = Walk {
            gv,
            scopes: vec![Vec::new()],
            loops: vec![LoopT {
                exit: end,
                next: end,
                carry: None,
            }],
            depth: None,
            snaps: std::collections::HashMap::new(),
            is_fn: true,
            end_block: end,
            ended: false,
        };
        // seed the scope with the captures (snapshot order), then the inputs
        let mut pi = 0usize;
        for (cn, ck) in plan.caps.iter() {
            let k = *ck;
            let var = builder.declare_var(k.ty());
            builder.def_var(var, params[pi]);
            w.scopes[0].push((cn.clone(), Bind { var, kind: k }));
            pi += 1;
        }
        for (j, t) in plan.def.input_types.iter().enumerate() {
            let Some(sem::ParamType::K(kind)) = t else {
                unreachable!()
            };
            let s = kind_scalar(kind).unwrap();
            let var = builder.declare_var(s.ty());
            builder.def_var(var, params[pi + j]);
            let name = plan.def.inputs[j].0.clone();
            w.scopes[0].push((name, Bind { var, kind: s }));
        }
        let dvar = builder.declare_var(WORD);
        builder.def_var(dvar, params[pi + plan.def.inputs.len()]);
        w.depth = Some(dvar);

        let stmts: Option<&[sem::Stmt]> = match &plan.def.body {
            sem::FnBody::Block(s) => Some(s),
            // one-line closure (`give <expr>`): emit and hand back
            sem::FnBody::Expr(e) => {
                let v = self.eval_expr(prog, &mut builder, &mut w, e)?;
                builder.ins().return_(&[v]);
                w.ended = true;
                None
            }
        };
        if let Some(stmts) = stmts {
            self.walk_stmts(prog, &mut builder, &mut w, stmts)?;
        }
        if !w.ended {
            // unreachable in a scanned program; return the kind's zero
            // defensively so the machine function always terminates
            let z = match plan.ret {
                Scalar::Whole => builder.ins().iconst(WORD, 0),
                Scalar::Boolean => builder.ins().iconst(BOOL, 0),
                Scalar::Decimal => builder.ins().f64const(Ieee64::with_float(0.0)),
            };
            builder.ins().return_(&[z]);
        }
        builder.seal_all_blocks();
        builder.finalize();
        if std::env::var_os("Lykaon_IR").is_some() {
            eprintln!("=== IR of closure '{}'\n{}", plan.name, ctx.func.display());
        }
        self.module
            .define_function(fid, &mut ctx)
            .map_err(|e| format!("compiling the local function '{}': {e:?}", plan.name))?;
        Ok(())
    }

    fn compile_main(&mut self, prog: &sem::Program, main_id: FuncId) -> Result<(), String> {
        let sig = self.fn_sig(0, Some(RET));
        let mut ctx = Context::new();
        ctx.func = Function::with_name_signature(UserFuncName::user(0, main_id.as_u32()), sig);
        let mut fctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        let gv = self
            .module
            .declare_data_in_func(self.pool.unwrap(), &mut builder.func);
        let end = builder.create_block();
        builder.switch_to_block(entry);

        let mut w = Walk {
            gv,
            scopes: vec![Vec::new()],
            loops: vec![LoopT {
                exit: end,
                next: end,
                carry: None,
            }],
            depth: None,
            snaps: std::collections::HashMap::new(),
            is_fn: false,
            end_block: end,
            ended: false,
        };
        // the top-level body runs at interpreter depth 0: its calls pass a
        // literal zero (interp.rs: depth starts at 0 and only calls bump it)
        self.walk_stmts(prog, &mut builder, &mut w, &prog.body)?;
        if !w.ended {
            builder.ins().jump(end, &[]);
        }
        builder.switch_to_block(end);
        self.rt(&mut builder, RT_FLUSH, &[], None, &[])?;
        let z = builder.ins().iconst(WORD, 0);
        let z32 = builder.ins().ireduce(RET, z);
        builder.ins().return_(&[z32]);
        builder.seal_all_blocks();
        builder.finalize();
        self.module
            .define_function(main_id, &mut ctx)
            .map_err(|e| format!("compiling main: {e:?}"))?;
        Ok(())
    }

    // ------------------------------------------------- symbol references

    fn declare_rt(
        &mut self,
        func: &mut ir::Function,
        name: &'static str,
        params: &[ir::Type],
        ret: Option<ir::Type>,
    ) -> ir::FuncRef {
        let id = if !self.rt_fns.contains_key(name) {
            let sig = self.sig_from(params.to_vec(), ret);
            let id = self
                .module
                .declare_function(name, Linkage::Import, &sig)
                .expect("declare rt function");
            self.rt_fns.insert(name, id);
            id
        } else {
            self.rt_fns[name]
        };
        self.module.declare_func_in_func(id, func)
    }

    fn declare_user(&mut self, func: &mut ir::Function, name: &str) -> Result<ir::FuncRef, String> {
        let Some(id) = self.user_fns.get(name).copied() else {
            return Err(format!(
                "internal: the call to '{name}' is not a lowered function"
            ));
        };
        Ok(self.module.declare_func_in_func(id, func))
    }

    // ------------------------------------------------- runtime call glue

    /// Call a runtime function; returns its word result when declared with
    /// one (rt functions take and return i64 words; f64 values ride their
    /// bits through `bitcast`).
    fn rt(
        &mut self,
        builder: &mut FunctionBuilder,
        name: &'static str,
        params: &[ir::Type],
        ret: Option<ir::Type>,
        args: &[ir::Value],
    ) -> Result<Option<ir::Value>, String> {
        let fref = self.declare_rt(&mut builder.func, name, params, ret);
        let inst = builder.ins().call(fref, args);
        Ok(ret.map(|_| builder.func.dfg.inst_results(inst)[0]))
    }

    fn fail_if(
        &mut self,
        builder: &mut FunctionBuilder,
        gv: ir::GlobalValue,
        cond: ir::Value,
        f: Fail,
    ) -> Result<(), String> {
        let cont = builder.create_block();
        let fail = builder.create_block();
        builder.ins().brif(cond, fail, &[], cont, &[]);
        builder.switch_to_block(fail);
        let (off, len) = match f {
            Fail::Over => self.errs[0],
            Fail::DivZero => self.errs[1],
            Fail::Deep => self.errs[2],
        };
        let base = builder.ins().global_value(WORD, gv);
        let ptr = builder.ins().iadd_imm(base, off as i64);
        let l = builder.ins().iconst(WORD, len as i64);
        self.rt(builder, RT_FAIL, &[WORD, WORD], None, &[ptr, l])?;
        // rt_fail exits the process; this trap marks the block unreachable
        builder.ins().trap(ir::TrapCode::unwrap_user(1));
        builder.switch_to_block(cont);
        Ok(())
    }

    /// A text literal at its pool offset: pointer and length.
    fn str_ptr(
        &mut self,
        builder: &mut FunctionBuilder,
        gv: ir::GlobalValue,
        s: &str,
    ) -> (ir::Value, ir::Value) {
        let (off, len) = self.strings.add(s);
        let base = builder.ins().global_value(WORD, gv);
        let ptr = builder.ins().iadd_imm(base, off as i64);
        let l = builder.ins().iconst(WORD, len as i64);
        (ptr, l)
    }

    // ------------------------------------------------------ value walkers

    fn define_name(
        &mut self,
        builder: &mut FunctionBuilder,
        w: &mut Walk,
        name: &str,
        kind: Scalar,
        val: ir::Value,
    ) {
        // interp.rs Frame.define: replace in the current top scope
        let var = builder.declare_var(kind.ty());
        builder.def_var(var, val);
        let sc = w.scopes.last_mut().unwrap();
        sc.retain(|(n, _)| n != name);
        sc.push((name.to_string(), Bind { var, kind }));
    }

    fn bind_find(w: &Walk, name: &str) -> Option<Bind> {
        for s in w.scopes.iter().rev() {
            for (n, b) in s.iter().rev() {
                if n == name {
                    return Some(*b);
                }
            }
        }
        None
    }

    fn saturating_inc(&mut self, builder: &mut FunctionBuilder, x: ir::Value) -> ir::Value {
        // interp.rs: counters move with saturating_add(1); they cannot wrap
        let one = builder.ins().iconst(WORD, 1);
        let plus = builder.ins().iadd(x, one);
        let max = builder.ins().iconst(WORD, i64::MAX);
        let ismax = builder.ins().icmp(IntCC::Equal, x, max);
        builder.ins().select(ismax, max, plus)
    }

    fn as_i64_val(
        &mut self,
        builder: &mut FunctionBuilder,
        w: &Walk,
        kind: Scalar,
        v: ir::Value,
    ) -> Result<ir::Value, String> {
        // interp.rs as_i64: whole passes, decimals round half away from
        // zero, yes-or-no is 0/1
        match kind {
            Scalar::Whole => Ok(v),
            Scalar::Boolean => Ok(builder.ins().uextend(WORD, v)),
            Scalar::Decimal => {
                let bits = builder.ins().bitcast(WORD, ir::MemFlags::new(), v);
                let z = builder.ins().iconst(WORD, 0);
                Ok(self
                    .rt(builder, RT_ROUND, &[WORD, WORD], Some(WORD), &[bits, z])?
                    .unwrap())
            }
        }
    }

    fn to_f64(&mut self, builder: &mut FunctionBuilder, k: Scalar, v: ir::Value) -> ir::Value {
        match k {
            Scalar::Decimal => v,
            _ => builder.ins().fcvt_from_sint(FLT, v), // whole -> f64 like cmp_ord's numeric path
        }
    }

    /// Resolve an expression's scalar kind the same way the scanner does:
    /// a name carries its binding's kind, a call the callee's
    /// give-back-derived result kind, and anything else its own static
    /// kind. Without the name/call rules the sem layer's Unknown kinds
    /// would dead-end code the scanner accepted.
    fn kind_inner(&self, prog: &sem::Program, w: &Walk, inner: &Expr) -> Result<Scalar, String> {
        self.eval_kind(prog, w, inner)
    }

    fn eval_kind(&self, prog: &sem::Program, w: &Walk, e: &Expr) -> Result<Scalar, String> {
        match &e.e {
            E::Name(n) => Self::bind_find(w, n)
                .map(|b| b.kind)
                .ok_or_else(|| format!("internal: the name '{n}' has no binding")),
            // shape-op kinds the sem does not always stamp statically; the
            // scan fixed these kinds on acceptance, so mirror them here
            E::Neg(inner) => self.kind_inner(prog, w, inner),
            E::DivWhole(..) | E::Rem(..) | E::Pow(..) | E::Round(..) => Ok(Scalar::Whole),
            sem::E::AsWhole(..) => Ok(Scalar::Whole),
            sem::E::AsDecimal(..) => Ok(Scalar::Decimal),
            E::AndOr(..) | E::Compare(..) => Ok(Scalar::Boolean),
            E::Call { name, .. } => {
                // kinds the scan learned (stated or derived) resolve first;
                // e.kind last holds the sem's knowledge for the rest
                if let Some(k) = self.fn_kinds.get(name) {
                    return Ok(*k);
                }
                if let Some(f) = prog.funcs.iter().find(|f| f.name == *name) {
                    return fn_result_scalar(f).ok_or_else(|| {
                        format!("the result kind of '{name}' runs through the evaluator in M3")
                    });
                }
                // a local function (closure): the plan carries its result kind
                self.clo_plans
                    .iter()
                    .find(|p| p.name == *name)
                    .map(|p| p.ret)
                    .ok_or_else(|| format!("internal: no function '{name}'"))
            }
            _ => kind_scalar(&e.kind)
                .ok_or_else(|| format!("the kind of '{}' runs through the evaluator in M3", e.dis)),
        }
    }

    fn bin_op(
        &mut self,
        builder: &mut FunctionBuilder,
        w: &Walk,
        op: Op,
        ak: Scalar,
        av: ir::Value,
        bk: Scalar,
        bv: ir::Value,
    ) -> Result<ir::Value, String> {
        use Op as O;
        // decimals pair with decimals, and a whole anywhere in the pair is
        // promoted to f64 (interp.rs bin_op's numeric path); divided by zero
        // gives positive infinity, never a trap, in every decimal pairing
        if ak == Scalar::Decimal || bk == Scalar::Decimal {
            let fa = if ak == Scalar::Decimal {
                av
            } else {
                builder.ins().fcvt_from_sint(FLT, av)
            };
            let fb = if bk == Scalar::Decimal {
                bv
            } else {
                builder.ins().fcvt_from_sint(FLT, bv)
            };
            return Ok(match op {
                O::Plus => builder.ins().fadd(fa, fb),
                O::Minus => builder.ins().fsub(fa, fb),
                O::Time => builder.ins().fmul(fa, fb),
                O::DividedBy => {
                    let zero = builder.ins().f64const(Ieee64::with_float(0.0));
                    let isz = builder.ins().fcmp(FloatCC::Equal, fb, zero);
                    let q = builder.ins().fdiv(fa, fb);
                    let inf = builder.ins().f64const(Ieee64::with_float(f64::INFINITY));
                    builder.ins().select(isz, inf, q)
                }
                _ => return Err("internal: decimal pair the scanner does not accept".into()),
            });
        }
        if ak != Scalar::Whole || bk != Scalar::Whole {
            return Err("internal: mixed arithmetic the scanner does not accept".into());
        }
        // whole-number arithmetic: the interpreter's exact semantics
        match op {
            O::Plus => {
                let r = builder.ins().iadd(av, bv);
                // overflow when the sign hypothesis of add fails
                let x1 = builder.ins().bxor(r, av);
                let x2 = builder.ins().bxor(r, bv);
                let and = builder.ins().band(x1, x2);
                let z = builder.ins().iconst(WORD, 0);
                let ov = builder.ins().icmp(IntCC::SignedLessThan, and, z);
                self.fail_if(builder, w.gv, ov, Fail::Over)?;
                Ok(r)
            }
            O::Minus => {
                let r = builder.ins().isub(av, bv);
                let x1 = builder.ins().bxor(r, av);
                let x2 = builder.ins().bxor(av, bv);
                let and = builder.ins().band(x1, x2);
                let z = builder.ins().iconst(WORD, 0);
                let ov = builder.ins().icmp(IntCC::SignedLessThan, and, z);
                self.fail_if(builder, w.gv, ov, Fail::Over)?;
                Ok(r)
            }
            O::Time => {
                // checked asm is fully implemented by the rt call
                Ok(self
                    .rt(builder, RT_MUL, &[WORD, WORD], Some(WORD), &[av, bv])?
                    .unwrap())
            }
            O::DividedBy => {
                // the interpreter: x as f64 / y as f64 (a decimal)
                let fa = builder.ins().fcvt_from_sint(FLT, av);
                let fb2 = builder.ins().fcvt_from_sint(FLT, bv);
                Ok(builder.ins().fdiv(fa, fb2))
            }
            O::WrappingPlus => {
                let o = builder.ins().iconst(WORD, WADD);
                Ok(self
                    .rt(
                        builder,
                        RT_WRAP,
                        &[WORD, WORD, WORD],
                        Some(WORD),
                        &[o, av, bv],
                    )?
                    .unwrap())
            }
            O::WrappingMinus => {
                let o = builder.ins().iconst(WORD, WSUB);
                Ok(self
                    .rt(
                        builder,
                        RT_WRAP,
                        &[WORD, WORD, WORD],
                        Some(WORD),
                        &[o, av, bv],
                    )?
                    .unwrap())
            }
            O::WrappingTimes => {
                let o = builder.ins().iconst(WORD, WMUL);
                Ok(self
                    .rt(
                        builder,
                        RT_WRAP,
                        &[WORD, WORD, WORD],
                        Some(WORD),
                        &[o, av, bv],
                    )?
                    .unwrap())
            }
            O::SaturatingPlus => {
                let o = builder.ins().iconst(WORD, SADD);
                Ok(self
                    .rt(
                        builder,
                        RT_WRAP,
                        &[WORD, WORD, WORD],
                        Some(WORD),
                        &[o, av, bv],
                    )?
                    .unwrap())
            }
            O::SaturatingMinus => {
                let o = builder.ins().iconst(WORD, SSUB);
                Ok(self
                    .rt(
                        builder,
                        RT_WRAP,
                        &[WORD, WORD, WORD],
                        Some(WORD),
                        &[o, av, bv],
                    )?
                    .unwrap())
            }
            O::SaturatingTimes => {
                let o = builder.ins().iconst(WORD, SMUL);
                Ok(self
                    .rt(
                        builder,
                        RT_WRAP,
                        &[WORD, WORD, WORD],
                        Some(WORD),
                        &[o, av, bv],
                    )?
                    .unwrap())
            }
            _ => Err("internal: whole arithmetic the scanner does not accept".into()),
        }
    }

    /// One ordering relation (`less`, `more`, `at least`, `at most`) with the
    /// interpreter's cmp_ord numeric path: whole values convert to f64, and
    /// NaN counts as equal (so AtLeast/AtMost are true on NaN).
    fn cmp_order(
        &mut self,
        builder: &mut FunctionBuilder,
        w: &Walk,
        rel: Rel,
        lk: Scalar,
        lv: ir::Value,
        rk: Scalar,
        rv: ir::Value,
    ) -> Result<ir::Value, String> {
        let _ = w;
        if lk == Scalar::Whole && rk == Scalar::Whole {
            let cc = match rel {
                Rel::Less => IntCC::SignedLessThan,
                Rel::More => IntCC::SignedGreaterThan,
                Rel::AtLeast => IntCC::SignedGreaterThanOrEqual,
                Rel::AtMost => IntCC::SignedLessThanOrEqual,
                _ => unreachable!(),
            };
            Ok(builder.ins().icmp(cc, lv, rv))
        } else {
            let fa = self.to_f64(builder, lk, lv);
            let fb2 = self.to_f64(builder, rk, rv);
            let cc = match rel {
                Rel::Less => FloatCC::LessThan,
                Rel::More => FloatCC::GreaterThan,
                Rel::AtLeast => FloatCC::UnorderedOrGreaterThanOrEqual, // NaN = equal
                Rel::AtMost => FloatCC::UnorderedOrLessThanOrEqual,     // NaN = equal
                _ => unreachable!(),
            };
            Ok(builder.ins().fcmp(cc, fa, fb2))
        }
    }

    fn eval_compare(
        &mut self,
        prog: &sem::Program,
        builder: &mut FunctionBuilder,
        w: &Walk,
        c: &Comp,
    ) -> Result<ir::Value, String> {
        let lv = self.eval_expr(prog, builder, w, &c.l)?;
        let lk = self.eval_kind(prog, w, &c.l)?;
        let one = builder.ins().iconst(BOOL, 1);
        let raw = match c.rel {
            Rel::Equal | Rel::Not => {
                let rv0 = self.eval_expr(prog, builder, w, &c.r[0])?;
                let rk0 = self.eval_kind(prog, w, &c.r[0])?;
                match lk {
                    Scalar::Decimal => {
                        // cmp_eq has no (decimal, decimal) arm in interp.rs:
                        // `is` on decimals is always no. Both operands were
                        // still evaluated (they may print or fail).
                        builder.ins().iconst(BOOL, 0)
                    }
                    _ => {
                        let _ = rk0;
                        builder.ins().icmp(IntCC::Equal, lv, rv0)
                    }
                }
            }
            Rel::Less | Rel::More | Rel::AtLeast | Rel::AtMost => {
                let rv0 = self.eval_expr(prog, builder, w, &c.r[0])?;
                let rv0 = self.eval_expr(prog, builder, w, &c.r[0])?;
                let rk0 = self.eval_kind(prog, w, &c.r[0])?;
                self.cmp_order(builder, w, c.rel, lk, lv, rk0, rv0)?
            }
            Rel::Between => {
                let rv0 = self.eval_expr(prog, builder, w, &c.r[0])?;
                let rk0 = self.eval_kind(prog, w, &c.r[0])?;
                let rv1 = self.eval_expr(prog, builder, w, &c.r[1])?;
                let rk1 = self.eval_kind(prog, w, &c.r[1])?;
                let lo = self.cmp_order(builder, w, Rel::AtLeast, lk, lv, rk0, rv0)?;
                let hi = self.cmp_order(builder, w, Rel::AtMost, lk, lv, rk1, rv1)?;
                builder.ins().band(lo, hi)
            }
            _ => return Err("internal: comparison word the scanner rejected".into()),
        };
        // Compare: raw != negate (interp.rs), applied with one boolean flip
        if c.negate {
            Ok(builder.ins().bxor(raw, one))
        } else {
            Ok(raw)
        }
    }

    /// One call to another lowered function: inputs first (the interpreter
    /// evaluates them before run_fn_body touches the depth), then the T0607
    /// depth check, then the call with the hidden depth parameter.
    fn emit_call(
        &mut self,
        prog: &sem::Program,
        builder: &mut FunctionBuilder,
        w: &Walk,
        name: &str,
        args: &[Expr],
    ) -> Result<ir::Value, String> {
        let mut vs: Vec<ir::Value> = Vec::new();
        for a in args {
            vs.push(self.eval_expr(prog, builder, w, a)?);
        }
        let d = match w.depth {
            Some(var) => builder.use_var(var),
            None => builder.ins().iconst(WORD, 0), // the top level runs at depth 0
        };
        let one = builder.ins().iconst(WORD, 1);
        let d2 = builder.ins().iadd(d, one);
        let cap = builder.ins().iconst(WORD, MAX_DEPTH);
        let over = builder.ins().icmp(IntCC::SignedGreaterThan, d2, cap);
        self.fail_if(builder, w.gv, over, Fail::Deep)?;
        vs.push(d2);
        // a closure call also passes its capture values (interp.rs
        // eval_closure builds the frame as captures, then inputs); the scan
        // checked they are visible with the captured kinds here
        let plan = self
            .clo_plans
            .iter()
            .find(|p| p.name == name)
            .map(|p| (p.caps.clone(), p.def.inputs.len()));
        if let Some((caps, _n_args)) = plan {
            // The machine call passes the values captured when the `To`
            // sentence ran — the interpreter's frozen snapshot — then args,
            // then the depth (interp.rs eval_closure: captures, then inputs).
            let mut vals: Vec<ir::Value> = Vec::with_capacity(caps.len() + vs.len());
            for (cn, _) in &caps {
                // look up the snapshot register from the defining `To`
                let snap = w
                    .snaps
                    .get(name)
                    .and_then(|sv| sv.iter().find(|(n, _)| n == cn).map(|(_, v)| *v));
                match snap {
                    Some(v) => vals.push(builder.use_var(v)),
                    None => match Self::bind_find(w, cn) {
                        Some(b) => vals.push(builder.use_var(b.var)), // defensive: live value
                        None => {
                            return Err(format!(
                                "internal: the capture '{cn}' has no snapshot at the machine call to '{name}'"
                            ));
                        }
                    },
                }
            }
            // vs currently holds args + depth; split: args first
            let na = vs.len() - 1;
            vals.extend_from_slice(&vs[..na]);
            vals.push(vs[na]); // depth last
            let fref = self.declare_user(&mut builder.func, name)?;
            let inst = builder.ins().call(fref, &vals);
            return Ok(builder.func.dfg.inst_results(inst)[0]);
        }
        let fref = self.declare_user(&mut builder.func, name)?;
        let inst = builder.ins().call(fref, &vs);
        Ok(builder.func.dfg.inst_results(inst)[0])
    }

    fn eval_expr(
        &mut self,
        prog: &sem::Program,
        builder: &mut FunctionBuilder,
        w: &Walk,
        e: &Expr,
    ) -> Result<ir::Value, String> {
        match &e.e {
            E::Whole(x) => Ok(builder.ins().iconst(WORD, *x)),
            E::Dec(x) => Ok(builder.ins().f64const(Ieee64::with_float(*x))),
            E::Boolean(b) => Ok(builder.ins().iconst(BOOL, *b as i64)),
            E::Name(n) => match Self::bind_find(w, n) {
                Some(b) => Ok(builder.use_var(b.var)),
                None => Err(format!(
                    "internal: the name '{n}' is read where the scanner found none"
                )),
            },
            E::Neg(inner) => {
                let iv = self.eval_expr(prog, builder, w, inner)?;
                match kind_scalar(&inner.kind) {
                    Some(Scalar::Whole) => {
                        // checked negation: -(-9223372036854775808) fails
                        Ok(self
                            .rt(builder, RT_NEG, &[WORD], Some(WORD), &[iv])?
                            .unwrap())
                    }
                    Some(Scalar::Decimal) => {
                        let m1 = builder.ins().f64const(Ieee64::with_float(-1.0));
                        Ok(builder.ins().fmul(iv, m1))
                    }
                    _ => Err("internal: minus on a non-number scalar".into()),
                }
            }
            E::Binary { op, l, r } => {
                let av = self.eval_expr(prog, builder, w, l)?;
                let bv = self.eval_expr(prog, builder, w, r)?;
                let ak = self.eval_kind(prog, w, l)?;
                let bk = self.eval_kind(prog, w, r)?;
                self.bin_op(builder, w, *op, ak, av, bk, bv)
            }
            E::DivWhole(l, r) => {
                let av = self.eval_expr(prog, builder, w, l)?;
                let bv = self.eval_expr(prog, builder, w, r)?;
                Ok(self
                    .rt(builder, RT_DIVI, &[WORD, WORD], Some(WORD), &[av, bv])?
                    .unwrap())
            }
            E::Rem(l, r) => {
                let av = self.eval_expr(prog, builder, w, l)?;
                let bv = self.eval_expr(prog, builder, w, r)?;
                Ok(self
                    .rt(builder, RT_REM, &[WORD, WORD], Some(WORD), &[av, bv])?
                    .unwrap())
            }
            E::Pow(l, r) => {
                let av = self.eval_expr(prog, builder, w, l)?;
                let bv = self.eval_expr(prog, builder, w, r)?;
                let ak = self.eval_kind(prog, w, l)?;
                let bk = self.eval_kind(prog, w, r)?;
                let x = self.as_i64_val(builder, w, ak, av)?;
                let y = self.as_i64_val(builder, w, bk, bv)?;
                Ok(self
                    .rt(builder, RT_POW, &[WORD, WORD], Some(WORD), &[x, y])?
                    .unwrap())
            }
            E::Round(inner, even) => {
                let iv = self.eval_expr(prog, builder, w, inner)?;
                match self.eval_kind(prog, w, inner)? {
                    Scalar::Whole => Ok(iv), // whole values round to themselves
                    Scalar::Decimal => {
                        let bits = builder.ins().bitcast(WORD, ir::MemFlags::new(), iv);
                        let ev = builder.ins().iconst(WORD, if *even { 1 } else { 0 });
                        Ok(self
                            .rt(builder, RT_ROUND, &[WORD, WORD], Some(WORD), &[bits, ev])?
                            .unwrap())
                    }
                    Scalar::Boolean => Err("internal: nearest-to on yes-or-no".into()),
                }
            }
            E::AndOr(l, r, is_and) => {
                // the interpreter evaluates both sides (eval_expr for each);
                // no short-circuit
                let a = self.eval_expr(prog, builder, w, l)?;
                let b = self.eval_expr(prog, builder, w, r)?;
                Ok(if *is_and {
                    builder.ins().band(a, b)
                } else {
                    builder.ins().bor(a, b)
                })
            }
            sem::E::AsWhole(inner) => {
                // interp.rs: whole stays whole (the scanner only accepts a
                // whole inner; a decimal conversion can fail and is Embedded)
                let av = self.eval_expr(prog, builder, w, inner)?;
                debug_assert!(matches!(self.eval_kind(prog, w, inner)?, Scalar::Whole));
                Ok(av)
            }
            sem::E::AsDecimal(inner) => {
                // interp.rs: whole -> as f64, decimal passes through
                let av = self.eval_expr(prog, builder, w, inner)?;
                match self.eval_kind(prog, w, inner)? {
                    Scalar::Whole => Ok(builder.ins().fcvt_from_sint(FLT, av)),
                    Scalar::Decimal => Ok(av),
                    Scalar::Boolean => Err("internal: as decimal on yes-or-no".into()),
                }
            }
            E::Compare(c) => self.eval_compare(prog, builder, w, c),
            E::Call { name, args } => self.emit_call(prog, builder, w, name, args),
            other => Err(format!(
                "internal: expression shape the scanner accepted but the emitter cannot lower: {} ('{}'){}",
                other_name(other),
                e.dis,
                std::env::var_os("Lykaon_DEBUG_SCAN")
                    .map(|_| format!("\n{:?}\n", other))
                    .unwrap_or_default()
            )),
        }
    }

    // ------------------------------------------------------ output walkers

    fn say_scalar(
        &mut self,
        builder: &mut FunctionBuilder,
        kind: Scalar,
        v: ir::Value,
        places: i64,
        wt: ir::Value,
    ) -> Result<(), String> {
        match kind {
            Scalar::Whole => {
                self.rt(builder, RT_SAY_WHOLE, &[WORD, WORD], None, &[v, wt])?;
            }
            Scalar::Decimal => {
                let bits = builder.ins().bitcast(WORD, ir::MemFlags::new(), v);
                let pl = builder.ins().iconst(WORD, places);
                self.rt(
                    builder,
                    RT_SAY_DEC,
                    &[WORD, WORD, WORD],
                    None,
                    &[bits, pl, wt],
                )?;
            }
            Scalar::Boolean => {
                let b = builder.ins().uextend(WORD, v);
                self.rt(builder, RT_SAY_BOOL, &[WORD, WORD], None, &[b, wt])?;
            }
        }
        Ok(())
    }

    fn walk_say(
        &mut self,
        prog: &sem::Program,
        builder: &mut FunctionBuilder,
        w: &Walk,
        expr: &Expr,
        mods: &sem::SayMods,
        lines: &[String],
    ) -> Result<(), String> {
        let wt = builder
            .ins()
            .iconst(WORD, if mods.without_newline { 1 } else { 0 });
        let places = mods.places.unwrap_or(2) as i64;
        // literal lines only (the scan allows this shape alone)
        if !lines.is_empty() {
            for line in lines {
                let t = line.trim();
                let (ptr, l) = self.str_ptr(builder, w.gv, t);
                self.rt(
                    builder,
                    RT_SAY_TEXT,
                    &[WORD, WORD, WORD],
                    None,
                    &[ptr, l, wt],
                )?;
            }
            return Ok(());
        }
        // a bare word (`Say hi.`): the scan allows words alone here
        if let E::Word(t) = &expr.e {
            let (ptr, l) = self.str_ptr(builder, w.gv, t);
            self.rt(
                builder,
                RT_SAY_TEXT,
                &[WORD, WORD, WORD],
                None,
                &[ptr, l, wt],
            )?;
            return Ok(());
        }
        if let E::Flat(pieces) = &expr.e {
            if pieces.is_empty() {
                let (ptr, l) = self.str_ptr(builder, w.gv, "");
                self.rt(
                    builder,
                    RT_SAY_TEXT,
                    &[WORD, WORD, WORD],
                    None,
                    &[ptr, l, wt],
                )?;
                return Ok(());
            }
            // every piece is shown with one space between shown texts, then
            // the line's newline (interp.rs joins parts with " ")
            let one = builder.ins().iconst(WORD, 1);
            let zero = builder
                .ins()
                .iconst(WORD, if mods.without_newline { 1 } else { 0 });
            for (i, p) in pieces.iter().enumerate() {
                if i > 0 {
                    let (sp, sl) = self.str_ptr(builder, w.gv, " ");
                    self.rt(
                        builder,
                        RT_SAY_TEXT,
                        &[WORD, WORD, WORD],
                        None,
                        &[sp, sl, one],
                    )?;
                }
                if let E::Word(t) = &p.e {
                    let (ptr, l) = self.str_ptr(builder, w.gv, t);
                    self.rt(
                        builder,
                        RT_SAY_TEXT,
                        &[WORD, WORD, WORD],
                        None,
                        &[ptr, l, one],
                    )?;
                    continue;
                }
                let v = self.eval_expr(prog, builder, w, p)?;
                let kind = self.eval_kind(prog, w, p)?;
                self.say_scalar(builder, kind, v, places, one)?;
            }
            // the newline (an empty text with without=0)
            let (ptr, l) = self.str_ptr(builder, w.gv, "");
            self.rt(
                builder,
                RT_SAY_TEXT,
                &[WORD, WORD, WORD],
                None,
                &[ptr, l, zero],
            )?;
            return Ok(());
        }
        let v = self.eval_expr(prog, builder, w, expr)?;
        let kind = self.eval_kind(prog, w, expr)?;
        self.say_scalar(builder, kind, v, places, wt)
    }

    // ------------------------------------------------------ control wheels

    fn walk_stmts(
        &mut self,
        prog: &sem::Program,
        builder: &mut FunctionBuilder,
        w: &mut Walk,
        stmts: &[sem::Stmt],
    ) -> Result<(), String> {
        for st in stmts {
            if w.ended {
                // the interpreter's exec_stmts returns early on Stop, Skip
                // and give backs; everything after is unreachable
                break;
            }
            self.walk_stmt(prog, builder, w, st)?;
        }
        Ok(())
    }

    fn walk_stmt(
        &mut self,
        prog: &sem::Program,
        builder: &mut FunctionBuilder,
        w: &mut Walk,
        st: &sem::Stmt,
    ) -> Result<(), String> {
        match st {
            sem::Stmt::Note => Ok(()),
            sem::Stmt::Define(d) => {
                let v = self.eval_expr(prog, builder, w, &d.expr)?;
                let kind = self.eval_kind(prog, w, &d.expr)?;
                self.define_name(builder, w, &d.name, kind, v);
                Ok(())
            }
            sem::Stmt::DefineLocalFn(f) => {
                // The machine form of the interpreter's DefineLocalFn sentence:
                // copy each captured variable's current value into a snapshot
                // register (interp.rs freezes exactly these values at this
                // sentence). The statement itself binds nothing the walk reads;
                // call sites use the snapshots.
                let plan = match self.clo_plans.iter().find(|p| p.name == f.name) {
                    Some(p) => p.clone(),
                    None => {
                        return Err(format!(
                            "internal: the local function '{}' has no machine plan",
                            f.name
                        ));
                    }
                };
                let mut snap: Vec<(String, Variable)> = Vec::new();
                for (cn, ck) in &plan.caps {
                    let cur = match Self::bind_find(w, cn) {
                        Some(b) => builder.use_var(b.var),
                        None => {
                            return Err(format!(
                                "internal: the capture '{cn}' of '{}' has no binding where it is defined",
                                f.name
                            ));
                        }
                    };
                    let var = builder.declare_var(ck.ty());
                    builder.def_var(var, cur);
                    snap.push((cn.clone(), var));
                }
                w.snaps.insert(plan.name.clone(), snap);
                Ok(())
            }
            sem::Stmt::Set { name, expr } => {
                let v = self.eval_expr(prog, builder, w, expr)?;
                let kind = self.eval_kind(prog, w, expr)?;
                // Frame.assign: update the scope that owns the name; if none
                // does, define it into the last scope. CRITICAL for loops:
                // `Set total to total plus 1` inside `Repeat N times` must
                // reassign the SAME variable (a loop-carried def), not bind
                // the name to a fresh var. A fresh var breaks accumulation:
                // every iteration reads the original def (plus the loop
                // condition of `Repeat while` would read a never-changing
                // variable and hang).
                let mut placed = false;
                for s in w.scopes.iter_mut().rev() {
                    if let Some(idx) = s.iter().position(|(n, _)| n == name) {
                        let existing = s[idx].1;
                        if existing.kind.ty() == kind.ty() {
                            // same Cranelift type: reassign the existing var
                            builder.def_var(existing.var, v);
                            s[idx] = (
                                name.to_string(),
                                Bind {
                                    var: existing.var,
                                    kind,
                                },
                            );
                        } else {
                            // kind changed on assign: fresh var (values may
                            // leave the loop legitimately; loop-carried
                            // retyping is not representable in one var)
                            let var = builder.declare_var(kind.ty());
                            builder.def_var(var, v);
                            s[idx] = (name.to_string(), Bind { var, kind });
                        }
                        placed = true;
                        break;
                    }
                }
                if !placed {
                    let var = builder.declare_var(kind.ty());
                    builder.def_var(var, v);
                    w.scopes
                        .last_mut()
                        .unwrap()
                        .push((name.to_string(), Bind { var, kind }));
                }
                Ok(())
            }
            sem::Stmt::Say { expr, mods, lines } => {
                self.walk_say(prog, builder, w, expr, mods, lines)
            }
            sem::Stmt::If { branches, other } => {
                let merge = builder.create_block();
                // does every branch end the flow (a give back, Stop, Stop
                // inside a loop...)? Then only the not-taken path may still
                // reach the merge block.
                let mut every_ended = true;
                for (cond, body) in branches {
                    // interp.rs eval_expr runs the whole condition first, so
                    // no short-circuit across the branch chain
                    let cv = self.eval_expr(prog, builder, w, cond)?;
                    let bb = builder.create_block();
                    let cont = builder.create_block();
                    builder.ins().brif(cv, bb, &[], cont, &[]);
                    builder.switch_to_block(bb);
                    w.scopes.push(Vec::new());
                    self.walk_stmts(prog, builder, w, body)?;
                    w.scopes.pop();
                    if w.ended {
                        // this branch ends its path; the not-taken path
                        // (through cont) must not join the ended state
                        w.ended = false;
                    } else {
                        every_ended = false;
                        builder.ins().jump(merge, &[]);
                    }
                    builder.switch_to_block(cont);
                }
                // the not-taken path: the all-conditions-false edge lands
                // here, and it continues exactly where the interpreter left
                // off (into any Otherwise block, then past the If)
                let mut stopped = false;
                if let Some(ob) = other {
                    w.scopes.push(Vec::new());
                    self.walk_stmts(prog, builder, w, ob)?;
                    w.scopes.pop();
                    stopped = w.ended;
                    w.ended = false;
                }
                if !stopped {
                    builder.ins().jump(merge, &[]);
                }
                w.ended = stopped && every_ended;
                builder.switch_to_block(merge);
                Ok(())
            }
            sem::Stmt::RepeatTimes { count, body } => {
                let lv = self.eval_expr(prog, builder, w, count)?;
                let lk = self.eval_kind(prog, w, count)?;
                let lim = self.as_i64_val(builder, w, lk, lv)?;
                let header = builder.create_block();
                let bodyb = builder.create_block();
                let next = builder.create_block();
                let after = builder.create_block();
                let c0 = builder.ins().iconst(WORD, 1);
                builder.ins().jump(header, &bar1(c0));
                builder.switch_to_block(header);
                let cb = builder.append_block_param(header, WORD);
                let done = builder.ins().icmp(IntCC::SignedGreaterThan, cb, lim);
                builder.ins().brif(done, after, &[], bodyb, &bar1(cb));
                builder.switch_to_block(bodyb);
                let cbody = builder.append_block_param(bodyb, WORD);
                w.loops.push(LoopT {
                    exit: after,
                    next,
                    carry: Some(cbody),
                });
                w.scopes.push(Vec::new());
                self.walk_stmts(prog, builder, w, body)?;
                w.scopes.pop();
                w.loops.pop();
                if !w.ended {
                    builder.ins().jump(next, &bar1(cbody));
                }
                w.ended = false;
                builder.switch_to_block(next);
                let cn = builder.append_block_param(next, WORD);
                let c2 = self.saturating_inc(builder, cn);
                builder.ins().jump(header, &bar1(c2));
                builder.switch_to_block(after);
                Ok(())
            }
            sem::Stmt::RepeatForever { body } => {
                let start = builder.create_block();
                let after = builder.create_block();
                builder.ins().jump(start, &[]);
                builder.switch_to_block(start);
                w.loops.push(LoopT {
                    exit: after,
                    next: start,
                    carry: None,
                });
                w.scopes.push(Vec::new());
                self.walk_stmts(prog, builder, w, body)?;
                w.scopes.pop();
                w.loops.pop();
                if !w.ended {
                    builder.ins().jump(start, &[]);
                }
                w.ended = false;
                builder.switch_to_block(after);
                Ok(())
            }
            sem::Stmt::RepeatWhile { cond, body } => {
                let start = builder.create_block();
                let bodyb = builder.create_block();
                let after = builder.create_block();
                builder.ins().jump(start, &[]);
                builder.switch_to_block(start);
                // the condition runs in the outer scope every pass, like
                // exec_stmt's Repeat while (interp.rs)
                let cv = self.eval_expr(prog, builder, w, cond)?;
                builder.ins().brif(cv, bodyb, &[], after, &[]);
                builder.switch_to_block(bodyb);
                w.loops.push(LoopT {
                    exit: after,
                    next: start,
                    carry: None,
                });
                w.scopes.push(Vec::new());
                self.walk_stmts(prog, builder, w, body)?;
                w.scopes.pop();
                w.loops.pop();
                if !w.ended {
                    builder.ins().jump(start, &[]);
                }
                w.ended = false;
                builder.switch_to_block(after);
                Ok(())
            }
            sem::Stmt::ForRange {
                var,
                from,
                to,
                body,
            } => {
                let fv = self.eval_expr(prog, builder, w, from)?;
                let fk = self.eval_kind(prog, w, from)?;
                let tv = self.eval_expr(prog, builder, w, to)?;
                let tk = self.eval_kind(prog, w, to)?;
                let n0 = self.as_i64_val(builder, w, fk, fv)?;
                let e = self.as_i64_val(builder, w, tk, tv)?;
                let header = builder.create_block();
                let bodyb = builder.create_block();
                let next = builder.create_block();
                let after = builder.create_block();
                builder.ins().jump(header, &bar1(n0));
                builder.switch_to_block(header);
                let cn = builder.append_block_param(header, WORD);
                let done = builder.ins().icmp(IntCC::SignedGreaterThan, cn, e);
                builder.ins().brif(done, after, &[], bodyb, &bar1(cn));
                builder.switch_to_block(bodyb);
                let nb = builder.append_block_param(bodyb, WORD);
                w.loops.push(LoopT {
                    exit: after,
                    next,
                    carry: Some(nb),
                });
                // the loop variable is defined fresh into the pushed scope
                // on every pass (frame.define into the pass scope)
                let vv = builder.declare_var(WORD);
                builder.def_var(vv, nb);
                let mut sc = Vec::new();
                sc.push((
                    var.clone(),
                    Bind {
                        var: vv,
                        kind: Scalar::Whole,
                    },
                ));
                w.scopes.push(sc);
                self.walk_stmts(prog, builder, w, body)?;
                w.scopes.pop();
                w.loops.pop();
                if !w.ended {
                    builder.ins().jump(next, &bar1(nb));
                }
                w.ended = false;
                builder.switch_to_block(next);
                let cn2 = builder.append_block_param(next, WORD);
                let n2 = self.saturating_inc(builder, cn2);
                builder.ins().jump(header, &bar1(n2));
                builder.switch_to_block(after);
                Ok(())
            }
            sem::Stmt::GiveBack(vs) => {
                match vs {
                    Some(e) => {
                        let v = self.eval_expr(prog, builder, w, e)?;
                        if w.is_fn {
                            builder.ins().return_(&[v]);
                        } else {
                            // a top-level give back ends the program quietly
                            // (interp returns Flow::Hand; run prints the
                            // buffered output and reports success)
                            builder.ins().jump(w.end_block, &[]);
                        }
                    }
                    None => {
                        return Err(
                            "internal: give back without a value runs through the evaluator".into(),
                        );
                    }
                }
                w.ended = true;
                Ok(())
            }
            sem::Stmt::Stop => {
                let t = *w.loops.last().ok_or("internal: Stop with no loop")?;
                builder.ins().jump(t.exit, &[]);
                w.ended = true;
                Ok(())
            }
            sem::Stmt::Skip => {
                let t = *w.loops.last().ok_or("internal: Skip with no loop")?;
                match t.carry {
                    Some(c) => builder.ins().jump(t.next, &bar1(c)),
                    None => builder.ins().jump(t.next, &[]),
                };
                w.ended = true;
                Ok(())
            }
            other => Err(format!(
                "internal: statement the scanner accepted reaches the emitter ({})",
                long_word(other)
            )),
        }
    }
}

/// A short honest tag for an expression the emitter cannot lower (report
/// only; the scanner keeps these out of the Full path).
fn other_name(e: &E) -> &'static str {
    match e {
        E::It => "it",
        E::Them => "them",
        E::Factorial(_) => "factorial",
        E::CountIn(_) => "how many in",
        E::Lower(_) => "lower of",
        E::AsWhole(_) | E::AsDecimal(_) | E::AsBig(_) | E::AsText(_) | E::AsNumber(_) => "as ...",
        E::ListOf(_) => "a list",
        E::Flat(_) => "a sentence of several pieces",
        _ => "that shape",
    }
}
