//! The interpreter (M1b): runs the program by walking the typed tree that the
//! semantic layer built (the graph in Chapter 67: "statements become lists of
//! steps that jump to each other"). Each function call makes a fresh frame
//! with its own scope stack and loop counters, so Stop stays inside its own
//! loop, Skip jumps to the next pass, and Give back returns a value.

use crate::mir::{self, Step};
use crate::net;
use crate::sem::{self, E, Meaning, Op, Pat, Rel, SayMods, Value, gen_resume_safe};

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{BufRead as _, Write as _};

// ---- M3b contract prover (pass 1) hook ----
/// A hook the compiler installs (lykaon::prover): for one function, per Ensures
/// contract index, whether the condition is proven always true by interval
/// analysis over the function's MIR (ch.64, M3-S35). Proven-true means the
/// run-time evaluation of that condition could neither fail (T0603/T0604)
/// nor answer no, so the check is skipped; every unproven contract keeps
/// its run-time check.
pub type ProverHook = fn(&sem::FuncDef) -> std::sync::Arc<Vec<bool>>;
static PROVER_HOOK: std::sync::RwLock<Option<ProverHook>> = std::sync::RwLock::new(None);

/// Install the hook (idempotent: the last writer wins; the compiler calls
/// this once per process from its single compile funnel).
pub fn install_prover_hook(h: ProverHook) {
    *PROVER_HOOK.write().unwrap() = Some(h);
}

fn prover_hook() -> Option<ProverHook> {
    *PROVER_HOOK.read().unwrap()
}

/// A per-site Always hook (M3b pass 1, ch.64 M3-S38): the compiler installs
/// it (lykaon::prover). It receives one site's static facts ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬Ãƒâ€¦Ã‚Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â the kind name,
/// the part values knowable at the site (`(part name, value expression)`;
/// a record construction passes every part, a Set-part site only the
/// written part) ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬Ãƒâ€¦Ã‚Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â and the kind's Always conditions, and answers per
/// condition index whether the site is proven always true: the run-time
/// check at that site is then skipped. Every unproven condition keeps its
/// live check, so a skipped site can never smuggle a bad record through.
pub type AlwaysHook = fn(
    type_name: &str,
    parts: &[(String, sem::Expr)],
    conds: &[sem::Expr],
) -> std::sync::Arc<Vec<bool>>;
static ALWAYS_HOOK: std::sync::RwLock<Option<AlwaysHook>> = std::sync::RwLock::new(None);

/// Install the per-site Always hook (idempotent: the last writer wins; the
/// compiler calls this once per process from its single compile funnel).
pub fn install_always_hook(h: AlwaysHook) {
    *ALWAYS_HOOK.write().unwrap() = Some(h);
}

fn always_hook() -> Option<AlwaysHook> {
    *ALWAYS_HOOK.read().unwrap()
}

use unicode_segmentation::UnicodeSegmentation;

/// The grapheme clusters of a text, as the reader sees them (ch.14: UAX 29).
fn graphemes_of(t: &str) -> std::vec::IntoIter<&str> {
    t.graphemes(true).collect::<Vec<&str>>().into_iter()
}

pub struct RunError {
    pub message: String,
    /// M4-8: the process exit code the failure stands for (1 for the
    /// failures; the code of Exit with N. when the run ends through it,
    /// S77/S78; the signal codes without a handler, S79).
    pub code: i32,
    /// M4-8: the output printed before the run ended through Exit with N.
    /// (S77): the program's own words print, then the process ends with
    /// the code. The failure paths keep it empty (they print only their
    /// message, as before).
    pub out: String,
}

/// A catchable failure (a can-fail conversion, or a Fail.) or a
/// program-stopping error.
enum TErr {
    Signal,
    Fatal(String),
    /// M4-8 (Appendix K S77/S79): the run ends here with this exit code -
    /// `Exit with N.` or a signal arriving with no block registered. The
    /// active cleanups ran at the sentence that raised it.
    Exit(i64),
    /// A Hand back reached the top of a generator body run (ch.25): the
    /// value is the handed-back item.
    Yield(Value),
}

type R<T> = Result<T, TErr>;

/// Raised by the body of a loop or of a function.
enum Flow {
    Normal,
    Skip,
    Stop,
    Back(Value, bool), // Give back: (value, came from Fail.)
    Hand(Value),       // Hand back: one item from a generator (ch.25)
}

/// One scope frame: bindings in definition order so clean-up runs in reverse
/// order of definition (ch.31, M2-S41; M3-S29).
#[derive(Clone, Debug, Default)]
struct ScopeFrame {
    vars: HashMap<String, Value>,
    order: Vec<String>,
    /// M4-S22: the worker count set by "Use N workers." for Spread
    /// sentences in this scope and inner scopes; None = inherit (the
    /// default is the number of cores). Unobservable in the eager cut.
    workers: Option<usize>,
    /// M4-S38: temporary files created in this scope (Make temporary
    /// file.); the targets are removed when the scope ends, even after
    /// a failure.
    temps: Vec<std::path::PathBuf>,
}

/// M4 (Appendix K 7.4): one pending timer on the frame.
struct TimerTask {
    /// true = a one-shot After (M4-G14), false = a repeating Every (M4-G15).
    every: bool,
    /// The body block, shared so Frame stays cheap to clone.
    body: std::rc::Rc<Vec<sem::Stmt>>,
    /// After: fire once at/after this instant. Seed for Every: unused.
    deadline: std::time::Instant,
    /// Every: the fixed interval between round STARTS (M4-D12).
    interval: std::time::Duration,
    /// Every: the instant the next round starts.
    next_round: std::time::Instant,
    /// Every: Stop. inside a round ended it (M4-S26).
    stopped: bool,
    /// After: set true once the block has run once (M4-S25).
    done: bool,
}

impl Clone for TimerTask {
    fn clone(&self) -> Self {
        TimerTask {
            every: self.every,
            body: std::rc::Rc::clone(&self.body),
            deadline: self.deadline,
            interval: self.interval,
            next_round: self.next_round,
            stopped: self.stopped,
            done: self.done,
        }
    }
}

/// The 100 ms watcher beat (M4-S39: changes closer than 100 milliseconds
/// merge into one firing; the poll interval implements the merge).
const WATCH_POLL: std::time::Duration = std::time::Duration::from_millis(100);

/// M4 (Appendix K 7.5, M4-G47): one file watcher. The eager cut polls on
/// the same calendar as the timers (during Sleeps, 100 ms beat); a firing
/// body runs in a fresh pushed scope like a timer round.
struct WatcherTask {
    file: sem::FileRef,
    body: std::rc::Rc<Vec<sem::Stmt>>,
    /// The last observed file state: (exists, mtime, size).
    state: Option<(bool, Option<std::time::SystemTime>, u64)>,
    last_poll: std::time::Instant,
    /// Stop. inside the watcher body cancels the watcher (choice logged).
    stopped: bool,
}

impl Clone for WatcherTask {
    fn clone(&self) -> Self {
        WatcherTask {
            file: self.file.clone(),
            body: std::rc::Rc::clone(&self.body),
            state: self.state,
            last_poll: self.last_poll,
            stopped: self.stopped,
        }
    }
}

#[derive(Clone)]
struct Frame {
    scopes: Vec<ScopeFrame>,
    /// M4 (Appendix K): tasks visible in the current block frame, keyed by
    /// task name. Frame-level (not per-scope) so a task started inside a
    /// Do these together block stays waitable after the block (M4-D2); a
    /// task never outlives its enclosing function/call frame because a
    /// Wait for inside another function reaches its own Frame only.
    tasks: HashMap<String, TaskState>,
    /// M4 (Appendix K 7.4): pending timers (After/Every). Frame-level:
    /// the eager cut drives them off real-clock deadlines at Sleep passes
    /// and fires unfired Afters at main end; the pool increment moves
    /// them onto real workers.
    timers: Vec<TimerTask>,
    /// M4 (Appendix K 7.5): file watchers (When file F changes.); polled
    /// on the timer calendar during Sleeps (M4-G47, eager cut).
    watchers: Vec<WatcherTask>,
    /// Repeat times / For each from: (current pass, limit).
    counters: Vec<(i64, i64)>,
    /// Ch.16 pronouns: the result of the sentence just before.
    last_result: Option<Value>,
    /// What the previous sentence printed, for the T0220 message.
    last_shown: String,
    /// M3 (ch.24, Reference 3 rule 30): inside a where condition, it is the
    /// item being tested. Set while the condition runs; it wins over
    /// last_result so a list item can be examined with it.
    where_item: Option<Value>,
}

impl Frame {
    fn push(&mut self) {
        self.scopes.push(ScopeFrame::default());
    }
    /// Drop the top scope and return its bindings in definition order, so
    /// clean-up can run in reverse order (ch.31).
    fn pop(&mut self) -> Option<ScopeFrame> {
        self.scopes.pop()
    }
    fn find(&self, name: &str) -> Option<&Value> {
        for sc in self.scopes.iter().rev() {
            if let Some(v) = sc.vars.get(name) {
                return Some(v);
            }
        }
        None
    }
    fn find_mut(&mut self, name: &str) -> Option<&mut Value> {
        for sc in self.scopes.iter_mut().rev() {
            if sc.vars.contains_key(name) {
                return sc.vars.get_mut(name);
            }
        }
        None
    }
    fn assign(&mut self, name: &str, v: Value) {
        for sc in self.scopes.iter_mut().rev() {
            if sc.vars.contains_key(name) {
                *sc.vars.get_mut(name).unwrap() = v;
                return;
            }
        }
        if let Some(sc) = self.scopes.last_mut() {
            sc.vars.insert(name.to_string(), v);
        }
    }
    fn define(&mut self, name: &str, v: Value) {
        match self.scopes.last_mut() {
            Some(sc) => {
                if !sc.order.iter().any(|n| n == name) {
                    sc.order.push(name.to_string());
                }
                sc.vars.insert(name.to_string(), v);
            }
            None => {
                let mut sc = ScopeFrame::default();
                sc.order.push(name.to_string());
                sc.vars.insert(name.to_string(), v);
                self.scopes.push(sc);
            }
        }
    }
}

impl<'p> Interp<'p> {
    /// Run clean-up blocks for the values of a dropped scope (ch.31,
    /// M3-S29), in reverse order of definition. A value is cleaned up when
    /// its kind declares `can clean up`; inside the block, the value is
    /// bound under its kind's name and nothing else. Errors inside a
    /// clean-up block are swallowed: they never replace an earlier failure.
    fn run_cleanups(&mut self, scope: ScopeFrame, out: &mut String) {
        for name in scope.order.iter().rev() {
            let Some(v) = scope.vars.get(name) else {
                continue;
            };
            let Value::Record(tname, _) = v else { continue };
            let Some(impl_block) = self
                .prog
                .impls
                .iter()
                .find(|i| i.kind_name == *tname && i.meaning == Some(Meaning::CleanUp))
            else {
                continue;
            };
            // The clean-up block sees the value under its kind's name and
            // nothing else (ch.31: "Using it inside a clean-up block" is a
            // mistake).
            let mut fr = Frame {
                scopes: vec![ScopeFrame {
                    vars: HashMap::from([(tname.clone(), v.clone())]),
                    order: vec![tname.clone()],
                    workers: None,
                    temps: Vec::new(),
                }],
                tasks: HashMap::new(),
                counters: Vec::new(),
                last_result: None,
                last_shown: String::new(),
                where_item: None,
                timers: Vec::new(),
                watchers: Vec::new(),
            };
            // errors inside clean-up never replace an earlier failure
            let _ = self.exec_stmts(&impl_block.body, &mut fr, out);
        }
        // M4-S38: a temporary file is removed when the block that holds it
        // ends, even after a failure (deletion problems are swallowed:
        // clean-up must not replace an earlier failure)
        for path in &scope.temps {
            let _ = std::fs::remove_file(path);
        }
    }

    /// Check the Always invariants of one kind against a record's parts
    /// (ch.64, M3-S38). The condition reads the parts of the record by name,
    /// in a fresh frame. Violation: a fatal error in the shape of the
    /// contract failures (ch.64). `site` carries the M3b per-site skip
    /// decision: the site's Expr address (races as a cache key for one
    /// Interp lifetime) and the part value expressions knowable there, or
    /// `None` where no static facts exist.
    fn run_always(
        &mut self,
        type_name: &str,
        parts: &[(String, Value)],
        site: Option<(usize, &[(String, sem::Expr)])>,
        out: &mut String,
    ) -> R<()> {
        let checks: Vec<(sem::Expr, String)> = self
            .prog
            .always
            .iter()
            .filter(|(tn, _)| tn == type_name)
            .map(|(_, c)| (c.cond.clone(), c.text.clone()))
            .collect();
        let skips: Vec<bool> = match site {
            Some((key, site_parts)) => self.always_site_skips(key, type_name, site_parts, &checks),
            None => vec![false; checks.len()],
        };
        'conds: for (idx, (cond, text)) in checks.into_iter().enumerate() {
            // M3b pass 1: a condition PROVEN always true at this site is
            // skipped; every other one keeps its live check.
            if skips.get(idx).copied().unwrap_or(false) {
                continue 'conds;
            }
            let mut fr = Frame {
                scopes: Vec::new(),
                counters: Vec::new(),
                last_result: None,
                last_shown: String::new(),
                where_item: None,
                tasks: HashMap::new(),
                timers: Vec::new(),
                watchers: Vec::new(),
            };
            let mut sc = ScopeFrame::default();
            for (n, v) in parts {
                sc.vars.insert(n.clone(), v.clone());
                sc.order.push(n.clone());
            }
            // Full value access (ch.64): the whole record value is bound
            // under the kind name, `value` and `original`, so a condition
            // like `age of value is at least 0` reads inside the value. A
            // part named the same keeps its own binding.
            let whole = Value::Record(type_name.to_string(), parts.to_vec());
            for name in [type_name, "value", "original"] {
                if !parts.iter().any(|(n, _)| n == name) {
                    sc.vars.insert(name.to_string(), whole.clone());
                    sc.order.push(name.to_string());
                }
            }
            fr.scopes.push(sc);
            let cv = self.eval_expr(&cond, &mut fr, out)?;
            if !is_truthy(&cv) {
                let t2 = text.trim().trim_start_matches("Always ").trim();
                let body = t2;
                return Err(fatal(
                    "T0602",
                    &format!("Always failed: {body}."),
                    "The kind's Always line does not allow this value.",
                ));
            }
        }
        Ok(())
    }

    /// Per-site Always skip decisions (M3b pass 1): asked the prover's
    /// per-site hook once per site and cached for the Interp lifetime ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬Ãƒâ€¦Ã‚Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â
    /// the site's `site` key is an address inside the `prog` tree this
    /// Interp borrows, so it stays valid. No hook (or the off switch inside
    /// the hook) answers all-false: every check stays live.
    fn always_site_skips(
        &self,
        site: usize,
        type_name: &str,
        parts: &[(String, sem::Expr)],
        checks: &[(sem::Expr, String)],
    ) -> Vec<bool> {
        let cached = self.proven_sites.borrow().get(&site).cloned();
        if let Some(a) = cached {
            return a.as_ref().clone();
        }
        let conds: Vec<sem::Expr> = checks.iter().map(|(c, _)| c.clone()).collect();
        let v = match self.prover_always {
            Some(h) => h(type_name, parts, &conds).as_ref().clone(),
            None => vec![false; conds.len()],
        };
        self.proven_sites
            .borrow_mut()
            .insert(site, std::sync::Arc::new(v.clone()));
        v
    }
}

/// M4-10 (Appendix K 7.8): the ambient context of the request handler
/// (or live connection) whose body is running. The `request` reads go
/// through the E::RequestRead rows, `session` is the provided map value,
/// Respond stashes the answer here, and the live connection is shared
/// with the WsSend/WsRecv sentences. The eager model runs the body
/// inline on the server loop, like Start task.
struct HandlerCtx {
    /// The request's method word, upper case ("GET").
    method: String,
    /// The page NAME that matched (page of request).
    page: String,
    /// The matched path's parameter values (anything called NAME), in
    /// declaration order.
    params: Vec<(String, String)>,
    /// The request's query pairs, decoded.
    query: Vec<(String, String)>,
    /// The request's headers, keys lower-cased.
    headers: Vec<(String, String)>,
    /// The request body bytes.
    body: Vec<u8>,
    /// The session map (text to text) with its cookie; a new session
    /// rides home as Set-Cookie on the response.
    session: Value,
    cookie: String,
    session_new: bool,
    /// The response Respond stashed (None until then).
    response: Option<net::ServerResponse>,
    /// The live connection (When someone opens live): shared with
    /// WsSend (write) and WsRecv (read).
    ws: Option<std::rc::Rc<std::cell::RefCell<net::WsStream>>>,
}

/// M4-S73/D13 (route A): one parked or running live session. The body
/// runs as a resumable block graph against the SERVER frame (its own
/// scopes push on entry and pop at every park), so a top-level
/// collection is one shared value that a broadcast can read.
struct LiveSession {
    /// The connection's id (the value `connection` holds).
    id: u64,
    /// The upgraded socket.
    conn: std::rc::Rc<std::cell::RefCell<net::WsStream>>,
    /// Bytes read off the socket that no frame has consumed yet.
    pending: Vec<u8>,
    /// True once the peer closed (observed at a read): the session
    /// ends at the next Receive (S73).
    closed: bool,
    /// The body's block graph, built once at the handshake.
    mir: std::sync::Arc<mir::ProgramMir>,
    /// Where the body starts in that graph.
    entry: usize,
    /// The resumable state: the program counter and loop counters.
    st: sem::GenState,
    /// The live page's name (the request rows read it).
    page: String,
    /// The path's parameter values (the request rows read them).
    params: Vec<(String, String)>,
    /// The session's own scopes, frozen while parked (outermost
    /// first). Empty before the first run.
    scopes: Vec<ScopeFrame>,
    /// The depth frame.scopes had when the session was created.
    base_depth: usize,
}

/// M4 (Appendix K): the life of a task entry in one frame. Running only
/// exists while the eager body runs; Done holds the give-back result
/// (Some = result waiting once, None = the task ended giving nothing);
/// Taken = the result was waited for, so a second move-wait is T0334.
#[derive(Clone, Debug)]
enum TaskState {
    Running,
    Done(Option<Value>),
    Taken,
}

/// M4-D14: does a value move when it is passed along? Mirrors the parse
/// side's `is_move_kind`: collections, records and shares move; plain
/// scalar values copy.
fn value_moves(v: &Value) -> bool {
    match v {
        Value::List(_)
        | Value::Map(_)
        | Value::Set(_)
        | Value::Queue(_)
        | Value::Record(_, _)
        | Value::Share(_) => true,
        Value::Pair(a, b) => value_moves(a) || value_moves(b),
        Value::Array(items) => items
            .iter()
            .any(|x| x.as_ref().map(value_moves).unwrap_or(false)),
        Value::Maybe(x) => x.as_ref().map(|v| value_moves(v)).unwrap_or(false),
        Value::Enum { parts, .. } => parts.iter().any(value_moves),
        Value::Dyn { value, .. } => value_moves(value),
        _ => false,
    }
}

/// M4-D3 reads: a name read of a guarded value is the guarded VALUE
/// (each read takes the lock and lets it go - the lock is unobservable
/// in the eager first cut); a read of an atomic or a counter is its
/// current number (M4-S19/S20: Say prints the value). A channel is NOT
/// unwrapped: both ends live in the one value, copies share the state.
fn unwrap_shared_read(v: Value) -> Value {
    match v {
        Value::Guarded(inner) => unwrap_shared_read(*inner),
        Value::Atomic(n) | Value::Counter(n) => Value::Whole(n),
        other => other,
    }
}

/// The milliseconds of an M4 duration value (M4-G4..G6, G14, G15):
/// plural units only; the shared beat of Sleep for, After and Every.
fn timer_unit_ms(amount: u64, unit: &str) -> u64 {
    match unit {
        "milliseconds" => amount,
        "seconds" => amount.saturating_mul(1000),
        "minutes" => amount.saturating_mul(60_000),
        "hours" => amount.saturating_mul(3_600_000),
        "days" => amount.saturating_mul(86_400_000),
        "weeks" => amount.saturating_mul(604_800_000),
        _ => amount,
    }
}

/// Instant::now() + ms, capped at about a year: a giant duration amount
/// would overflow the Instant and panic (deviation logged for M4-4:
/// huge timer amounts see the cap).
fn instant_after(ms: u64) -> std::time::Instant {
    const MAX_MS: u64 = 365 * 24 * 60 * 60 * 1000;
    std::time::Instant::now() + std::time::Duration::from_millis(ms.min(MAX_MS))
}

fn fatal(code: &str, cause: &str, fix: &str) -> TErr {
    TErr::Fatal(format!("Error: {cause} ({code})\nFix: {fix}"))
}

fn is_truthy(v: &Value) -> bool {
    as_truthy(v)
}

const T0603_C: &str = "A whole number went past 64 bits.";
const T0603_F: &str = "Use big number or checked plus.";
const T0604_C: &str = "A whole number was divided by zero.";
const T0604_F: &str = "Check the divisor.";
const T0607_C: &str = "Calls nested too deep.";
const T0607_F: &str = "Add a stop condition.";
const T0602_C: &str = "A contract failed.";
const T0602_F: &str = "Check the contract condition.";

fn not_allowed() -> TErr {
    fatal(
        "T0301",
        "A value of one kind is used where another is needed.",
        "Convert it with as.",
    )
}

struct Interp<'p> {
    prog: &'p sem::Program,
    input: String,
    in_pos: usize,
    budget: u64, // 0 = unlimited
    depth: usize,
    /// Pretend f gives V. overrides (ch.38), per test run.
    pretend: HashMap<String, Value>,
    /// Check failures collected while a test body runs.
    failed_checks: Vec<String>,
    in_must_fail: usize,
    /// While a generator body runs through the collect-all path (bodies
    /// whose Hand back sits in a nested execution, or a re-entrant pull of
    /// an already-running body), a Hand back is captured here instead of
    /// ending the run; the body runs to completion once (ch.25). Fully
    /// resumable bodies never touch these two fields.
    in_generator: bool,
    pending_hands: Vec<Value>,
    /// M4 (Appendix K): >0 while a timer block is running; a re-entrant
    /// calendar drive inside a firing round does nothing (deviation
    /// logged: nested timer events just real-sleep).
    timer_firing: usize,
    /// M4-G46: serial number for Make temporary file names (per run).
    temp_serial: u64,
    /// M4-7 (Appendix K S54): the program's random generator state, a
    /// xoshiro256++ state. None until the first random read; a run
    /// without Use seed seeds it from the operating system's entropy,
    /// a test run (run_test) seeds it with 42, and Use seed N. sets it
    /// by splitmix64 from N.
    rng: Option<[u64; 4]>,
    /// M4-8 (Appendix K 7.11): the tool's command-line bindings (Takes and
    /// Option values), seeded into the main scope before the body runs.
    bindings: Vec<(String, Value)>,
    /// M4-8 (S86): whether a person can be at the other end of standard
    /// input. False when standard input is not a terminal: Ask fails with
    /// kind other, the message being "no person here".
    interactive: bool,
    /// M4-8 (S79): the `When signal ... arrives.` blocks registered so
    /// far, in registration order. A signal's flag fires the FIRST block
    /// registered for it.
    signal_handlers: Vec<(sem::SignalName, Vec<sem::Stmt>)>,
    /// M4-S88: the run's log level. The order is debug < info < warning
    /// < error; the default is info, so debug lines are not written
    /// until `Use log level debug.` says otherwise.
    log_level: sem::LogLevel,
    /// M4-D11/D12: byte ranges of `out` that are standard error. Log
    /// lines are written into the one merged stream in order (lykaon test
    /// and the golden tests capture both streams as one), and these
    /// ranges let the real front ends split them again (the CLI and the
    /// built program write the range bytes to standard error).
    err_ranges: Vec<(usize, usize)>,
    /// M4-10 (Appendix K 7.8): the ambient context of the request
    /// handler (or live connection) whose body is running. `request`
    /// reads go through the E::RequestRead rows, `session` is the
    /// provided map value, Respond stashes the answer here, and the
    /// live connection is shared with WsSend/WsRecv. The eager model
    /// runs the body inline on the server loop, like Start task.
    handler_ctx: Option<HandlerCtx>,
    /// M4-10 (S72): the server's in-memory sessions, keyed by the
    /// cookie value, each with its last-seen time for the 30-minute
    /// expiry purge. Sessions are lost when the run ends.
    sessions: HashMap<String, (Value, std::time::SystemTime)>,
    /// M4-S73/D13 (route A): the live WebSocket sessions, one per
    /// upgraded connection, polled by the server's accept loop.
    live: Vec<LiveSession>,
    /// The id the next live connection gets.
    next_conn: u64,
    /// The live session running right now; its sentences resolve the
    /// provided `connection` value's socket through this id.
    active_conn: Option<u64>,
    /// Set by a live Receive when the frame is not here yet: the
    /// session executor parks the session at that statement (the
    /// statement re-runs on resume).
    park_conn: bool,
    /// Set when a live Receive observes the peer closed: the session
    /// ends after the statement that observed it (S73).
    end_session: bool,
    // ---- M3b contract prover (pass 1), installed by the compiler ----
    /// For one function, per Ensures contract index: whether the condition
    /// is proven always true by interval analysis; proven checks are
    /// skipped, unproven ones keep checking (ch.64, M3-S35).
    prover: Option<ProverHook>,
    /// Per-site Always hook (M3b pass 1), installed by the compiler.
    prover_always: Option<AlwaysHook>,
    /// Verdict cache keyed by (FuncDef address, name). Valid for one Interp
    /// lifetime: the `prog` borrow the interp holds outlives it, so the
    /// addresses stay stable while it is alive.
    proven: RefCell<HashMap<(usize, String), std::sync::Arc<Vec<bool>>>>,
    /// Per-site Always skip decisions keyed by the site's Expr address (a
    /// record construction node or the written-part element of a Set part
    /// statement). Valid for one Interp lifetime, same address argument.
    proven_sites: RefCell<HashMap<usize, std::sync::Arc<Vec<bool>>>>,
    /// M3c-4 transient buffer pool (see Pool below).
    pool: Pool,
}

// ============================================ M3c-4 transient buffer pool
//
// M3c-4 "arena" work, scoped honestly by the Value model: every Value
// owns its strings and lists OUTRIGHT (no Rc anywhere - Share is an
// emulated counted handle), so a literal bump arena over Values would be
// a rewrite of the ownership story, not a pass. What stays observable-
// free is a small free list of buffers for allocations whose VALUE
// NEVER ESCAPES the sentence that built it. Every buffer given back is
// cleared and size-capped, so neither content nor capacity can leak
// between users, and a leased buffer is never referenced after it goes
// back: the giveaway points all sit after the last read.
#[derive(Default)]
struct Pool {
    /// Say text assembly buffers.
    texts: Vec<String>,
    /// Say word-run part vectors (drained after the join).
    parts: Vec<Vec<String>>,
    /// ForIn iteration vecs for non-list payloads (drained per item).
    single: Vec<Vec<Value>>,
}
impl Pool {
    const MAX_SLOTS: usize = 8;
    const MAX_TEXT_BYTES: usize = 4096;
    const MAX_PARTS: usize = 128;
    const MAX_SINGLE: usize = 16;
    fn lease_text(&mut self) -> String {
        match self.texts.pop() {
            Some(mut s) => {
                s.clear();
                s
            }
            None => String::with_capacity(64),
        }
    }
    fn keep_text(&mut self, s: String) {
        if s.capacity() <= Self::MAX_TEXT_BYTES && self.texts.len() < Self::MAX_SLOTS {
            self.texts.push(s);
        }
    }
    fn lease_parts(&mut self) -> Vec<String> {
        match self.parts.pop() {
            Some(mut v) => {
                v.clear();
                v
            }
            None => Vec::new(),
        }
    }
    fn keep_parts(&mut self, v: Vec<String>) {
        if v.len() <= Self::MAX_PARTS && self.parts.len() < Self::MAX_SLOTS {
            self.parts.push(v);
        }
    }
    fn lease_single(&mut self) -> Vec<Value> {
        match self.single.pop() {
            Some(mut v) => {
                v.clear();
                v
            }
            None => Vec::new(),
        }
    }
    fn keep_single(&mut self, v: Vec<Value>) {
        if v.len() <= Self::MAX_SINGLE && self.single.len() < Self::MAX_SLOTS {
            self.single.push(v);
        }
    }
}

/// The outcome of one resumable generator-body execution (ch.25, M3-D12).
enum GHold {
    /// The body ended; it hands back no more items.
    Done,
    /// The body suspended at a Hand back; one item is appended to the cache.
    Hand(Value),
    /// M4-S73/D13 (route A): a live session parked at a Receive whose
    /// frame is not here yet. The program counter sits ON the Receive
    /// (it re-runs on resume); the executor froze the session's scopes.
    Parked,
}

/// A frozen interpreter frame, as the suspended state owns it.
fn frame_to_gen(fr: &Frame) -> sem::GenFrame {
    sem::GenFrame {
        scopes: fr
            .scopes
            .iter()
            .map(|s| {
                (
                    s.vars
                        .iter()
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect::<Vec<(String, Value)>>(),
                    s.order.clone(),
                )
            })
            .collect(),
        counters: fr.counters.clone(),
        last_result: fr.last_result.clone(),
        last_shown: fr.last_shown.clone(),
        where_item: fr.where_item.clone(),
    }
}

fn frame_from_gen(gf: sem::GenFrame) -> Frame {
    Frame {
        scopes: gf
            .scopes
            .into_iter()
            .map(|(vars, order)| ScopeFrame {
                vars: vars.into_iter().collect(),
                order,
                workers: None,
                temps: Vec::new(),
            })
            .collect(),
        tasks: HashMap::new(),
        counters: gf.counters,
        last_result: gf.last_result,
        last_shown: gf.last_shown,
        where_item: gf.where_item,
        timers: Vec::new(),
        watchers: Vec::new(),
    }
}

/// Run the program: the output text and the exit code (0, or the code of
/// Exit with N., or 1 for a failure). `bindings` seeds the tool's Takes
/// and Option values (M4-G25/G26); `interactive` says a person can be at
/// the other end of standard input (M4-S86). The failure message is part
/// of the text, with a trailing line feed, as before.
pub fn run(
    prog: &sem::Program,
    stdin_text: &str,
    bindings: &[(String, Value)],
    interactive: bool,
) -> (String, i32) {
    match run_budgeted(prog, stdin_text, 0, bindings, interactive) {
        Ok(out) => (out, 0),
        Err(e) => {
            // the failures print their message (with the trailing line
            // feed, as before); an Exit end prints the program's own
            // words and nothing else (the code carries the meaning)
            if e.message.is_empty() {
                (e.out, e.code)
            } else {
                (format!("{}\n", e.message), e.code)
            }
        }
    }
}

/// budget > 0 caps executed steps (used by the fuzzer). Also returns the
/// byte ranges of the merged output that are standard error (M4-D11/D12):
/// Log lines are written into the one merged stream in order, and the
/// real front ends (the CLI, the built program) split them again with
/// `split_streams`.
pub fn run_budgeted_streams(
    prog: &sem::Program,
    stdin_text: &str,
    budget: u64,
    bindings: &[(String, Value)],
    interactive: bool,
) -> (Result<String, RunError>, Vec<(usize, usize)>) {
    let mut it = Interp {
        prog,
        input: stdin_text.to_string(),
        in_pos: 0,
        budget,
        depth: 0,
        pretend: HashMap::new(),
        failed_checks: Vec::new(),
        in_must_fail: 0,
        in_generator: false,
        pending_hands: Vec::new(),
        timer_firing: 0,
        temp_serial: 0,
        rng: None,
        bindings: bindings.to_vec(),
        interactive,
        signal_handlers: Vec::new(),
        log_level: sem::LogLevel::Info,
        err_ranges: Vec::new(),
        handler_ctx: None,
        sessions: HashMap::new(),
        prover: prover_hook(),
        prover_always: always_hook(),
        proven: RefCell::new(HashMap::new()),
        proven_sites: RefCell::new(HashMap::new()),
        pool: Pool::default(),
        live: Vec::new(),
        next_conn: 0,
        active_conn: None,
        park_conn: false,
        end_session: false,
    };
    let mut frame = Frame {
        scopes: vec![ScopeFrame::default()],
        counters: Vec::new(),
        last_result: None,
        last_shown: String::new(),
        where_item: None,
        tasks: HashMap::new(),
        timers: Vec::new(),
        watchers: Vec::new(),
    };
    // M4-8 (M4-G25/G26): the tool's Takes and Option values are seeded
    // into the main scope before the body runs, in program order.
    for (n, v) in it.bindings.clone() {
        frame.define(&n, v);
    }
    let mut out = String::new();
    let run_result = it.exec_stmts(&prog.body, &mut frame, &mut out);
    // M4-S28: the program does not end while an After is still pending in
    // its main scope - the pending one-shot timers fire here (real
    // sleeps), and the Everies are cancelled with the main scope
    // (M4-S25/S26). Timers registered by a firing round are cancelled with
    // the scope of their registration (deviation logged).
    if run_result.is_ok() {
        let _ = it.fire_pending_afters(&mut frame, &mut out);
    }
    // Clean up top-level values at the end of the program (ch.31, M3-S29).
    if let Some(scope) = frame.pop() {
        let _ = it.run_cleanups(scope, &mut out);
    }
    let mut err_ranges = std::mem::take(&mut it.err_ranges);
    let result = match run_result {
        Ok(_) => Ok(out),
        // M4-8: Exit with N. (S77) and the no-handler signal end (S79) end
        // the run with their code; the active cleanups ran at the
        // sentence. The output printed so far goes out with it (S77: the
        // program's own words print, then the process ends).
        Err(TErr::Exit(code)) => Err(RunError {
            message: String::new(),
            code: code as i32,
            out,
        }),
        Err(TErr::Fatal(m)) => Err(RunError {
            message: m,
            code: 1,
            out: String::new(),
        }),
        Err(TErr::Signal) => Err(RunError {
            message: "Error: The program can fail here, and no fallback was written.".to_string(),
            code: 1,
            out: String::new(),
        }),
        Err(TErr::Yield(_)) => Err(RunError {
            message: "Error: Hand back runs outside a generator.".to_string(),
            code: 1,
            out: String::new(),
        }),
    };
    // M4-9: a failure that prints its message instead of the program's
    // output leaves the ranges pointing at text that is not returned -
    // drop them (the message belongs to the error stream anyway).
    if matches!(&result, Err(e) if !e.message.is_empty()) {
        err_ranges = Vec::new();
    }
    (result, err_ranges)
}

/// budget > 0 caps executed steps (used by the fuzzer). The output is the
/// one merged stream (M4-D11/D12): Log lines sit in it in order.
pub fn run_budgeted(
    prog: &sem::Program,
    stdin_text: &str,
    budget: u64,
    bindings: &[(String, Value)],
    interactive: bool,
) -> Result<String, RunError> {
    run_budgeted_streams(prog, stdin_text, budget, bindings, interactive).0
}

/// M4-D11/D12: split the one merged stream back into (standard output,
/// standard error) in order: the range bytes are the error stream, the
/// rest is the output stream.
pub fn split_streams(merged: &str, ranges: &[(usize, usize)]) -> (String, String) {
    let mut stdout_text = String::new();
    let mut stderr_text = String::new();
    let bytes = merged.as_bytes();
    let mut pos = 0usize;
    for &(start, end) in ranges {
        let (start, end) = (start.min(bytes.len()), end.min(bytes.len()));
        if start > pos {
            stdout_text.push_str(&merged[pos..start]);
        }
        stderr_text.push_str(&merged[start..end]);
        pos = pos.max(end);
    }
    if pos < merged.len() {
        stdout_text.push_str(&merged[pos..]);
    }
    (stdout_text, stderr_text)
}

// ---- M4-10 (Appendix K 7.8) free helpers -----------------------------------

/// The sem method word becomes the wire method (M4-S60).
fn wire_method(m: sem::NetMethod) -> net::Method {
    match m {
        sem::NetMethod::Get => net::Method::Get,
        sem::NetMethod::Post => net::Method::Post,
        sem::NetMethod::Put => net::Method::Put,
        sem::NetMethod::Delete => net::Method::Delete,
        sem::NetMethod::Patch => net::Method::Patch,
    }
}

/// A 200-shape text answer (Respond with x., status and text).
fn plain_response(status: u16, text: String) -> net::ServerResponse {
    net::ServerResponse {
        status,
        content_type: "text/plain; charset=utf-8".to_string(),
        body: text.into_bytes(),
        extra_headers: Vec::new(),
    }
}

/// The 500 internal error answer (M4-D15/S71).
fn internal_error_response() -> net::ServerResponse {
    net::ServerResponse {
        status: 500,
        content_type: "text/plain; charset=utf-8".to_string(),
        body: b"internal error".to_vec(),
        extra_headers: Vec::new(),
    }
}

/// The 404 not found answer (M4-S71).
fn not_found_response() -> net::ServerResponse {
    net::ServerResponse {
        status: 404,
        content_type: "text/plain; charset=utf-8".to_string(),
        body: b"not found".to_vec(),
        extra_headers: Vec::new(),
    }
}

/// Make shown text safe for HTML (S69): the ampersand, the angle
/// brackets and the quote marks become their entities.
fn html_safe(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            other => out.push(other),
        }
    }
    out
}

/// A session cookie value: 128 random bits as 32 hex characters. The
/// run's seeded generator is NOT used (Use seed 42. would make the
/// cookies predictable); the source is the hasher entropy of two fresh
/// RandomStates and the clock, mixed by the run's sha-1 (logged cut).
fn random_cookie_value() -> String {
    use std::hash::{BuildHasher, Hasher};
    let mut bytes = Vec::with_capacity(24);
    for _ in 0..2 {
        let h = std::collections::hash_map::RandomState::new()
            .build_hasher()
            .finish();
        bytes.extend_from_slice(&h.to_le_bytes());
    }
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0);
    bytes.extend_from_slice(&nanos.to_le_bytes());
    let digest = net::sha1(&bytes);
    let mut out = String::with_capacity(32);
    for b in digest {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// Does the request's path match a page's pattern (M4-S67)? The literal
/// segments compare lower-cased; an `anything called NAME` segment
/// captures the request's segment text. The lengths must agree.
fn match_pattern(pattern: &[sem::PageSeg], segments: &[String]) -> Option<Vec<(String, String)>> {
    if pattern.len() != segments.len() {
        return None;
    }
    let mut params = Vec::new();
    for (p, s) in pattern.iter().zip(segments.iter()) {
        match p {
            sem::PageSeg::Lit(word) => {
                if !word.eq_ignore_ascii_case(s) {
                    return None;
                }
            }
            sem::PageSeg::Param(name) => params.push((name.clone(), s.clone())),
        }
    }
    Some(params)
}

/// Run one test block (ch.38): executes its statements and collects the failed
/// checks. Returns the failed-check messages, or an error on a bug stop.
pub fn run_test(
    prog: &sem::Program,
    body: &[sem::Stmt],
    stdin_text: &str,
) -> Result<Vec<String>, RunError> {
    let mut it = Interp {
        prog,
        input: stdin_text.to_string(),
        in_pos: 0,
        budget: 0,
        depth: 0,
        pretend: HashMap::new(),
        failed_checks: Vec::new(),
        in_must_fail: 0,
        in_generator: false,
        pending_hands: Vec::new(),
        timer_firing: 0,
        temp_serial: 0,
        // M4-S54: tests use seed 42 unless a program sets another.
        rng: Some(crate::time4::xoshiro_seed(42)),
        // M4-8: tests run with no command line and (like the tool) a
        // person simulated by the caller; a Takes value reads missing.
        bindings: Vec::new(),
        interactive: true,
        signal_handlers: Vec::new(),
        log_level: sem::LogLevel::Info,
        err_ranges: Vec::new(),
        handler_ctx: None,
        sessions: HashMap::new(),
        prover: prover_hook(),
        prover_always: always_hook(),
        proven: RefCell::new(HashMap::new()),
        proven_sites: RefCell::new(HashMap::new()),
        pool: Pool::default(),
        live: Vec::new(),
        next_conn: 0,
        active_conn: None,
        park_conn: false,
        end_session: false,
    };
    let mut frame = Frame {
        scopes: vec![ScopeFrame::default()],
        counters: Vec::new(),
        last_result: None,
        last_shown: String::new(),
        where_item: None,
        tasks: HashMap::new(),
        timers: Vec::new(),
        watchers: Vec::new(),
    };
    let mut out = String::new(); // solver output inside tests is not part of the report
    let r = it.exec_stmts(body, &mut frame, &mut out);
    // M4-S28 for test blocks too: pending Afters fire at block end; the
    // Everies are cancelled with the block (M4-S25/S26).
    if r.is_ok() {
        let _ = it.fire_pending_afters(&mut frame, &mut out);
    }
    // Clean up values at the end of the test block (ch.31, M3-S29).
    if let Some(scope) = frame.pop() {
        let _ = it.run_cleanups(scope, &mut out);
    }
    match r {
        Ok(_) | Err(TErr::Signal) | Err(TErr::Yield(_)) => Ok(it.failed_checks),
        Err(TErr::Fatal(m)) => Err(RunError {
            message: m,
            code: 1,
            out: String::new(),
        }),
        // M4-8: Exit with N. inside a test block ends the block with that
        // code (logged: the checks so far stand).
        Err(TErr::Exit(_)) => Ok(it.failed_checks),
    }
}

impl<'p> Interp<'p> {
    fn tick(&mut self) -> R<()> {
        if self.budget == 0 {
            return Ok(());
        }
        if self.budget == 1 {
            return Err(TErr::Fatal(
                "Error: The program ran for too long.".to_string(),
            ));
        }
        self.budget -= 1;
        Ok(())
    }

    fn read_line(&mut self) -> String {
        let base = self.in_pos.min(self.input.len());
        let rest = &self.input[base..];
        let line = rest
            .split('\n')
            .next()
            .unwrap_or("")
            .trim_end_matches('\r')
            .to_string();
        self.in_pos = base + rest.find('\n').map(|i| i + 1).unwrap_or(rest.len());
        line
    }

    // ------------------------------------------------------------ statements

    /// M4-S79: the signal poll. One arrival is acted on per poll, in the
    /// fixed order interrupt, stop, hangup (the true arrival order is the
    /// OS's business and is not observable in the poll model - logged).
    /// With a block registered for the signal, the block runs as a task:
    /// its own scope, run eagerly inline at the poll (the eager cut -
    /// logged). With none, the active cleanups run and the run ends with
    /// the signal's exit code (interrupt 130, stop 143, hangup 129).
    // ---- M4-10 (Appendix K 7.8) network helpers ------------------------

    /// Fetch (M4-S60/S61): one HTTP request; the response record lands
    /// in it. A connection-level failure is the ordinary anonymous
    /// failure in this cut (the M4-5 file posture, logged).
    #[inline(never)]
    fn exec_fetch(
        &mut self,
        method: sem::NetMethod,
        address: &sem::NetAddress,
        data: Option<&sem::Expr>,
        headers: &[(String, sem::Expr)],
        query: &[(String, sem::Expr)],
        skip_tls: bool,
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Flow> {
        let data = match data {
            Some(e) => {
                let v = self.eval_expr(e, frame, out)?;
                // S60: text as text/plain; a record, list or map as
                // application/json; anything else as its shown wording.
                // A bytes body needs a distinct bytes kind (the bytes
                // value IS a list of whole), so a list goes as json -
                // logged.
                Some(match v {
                    Value::Text(t) => net::Data::Text(t),
                    Value::Record(..) | Value::Map(..) | Value::List(..) => {
                        let j = crate::formats::json_compact(&v).map_err(|_| TErr::Signal)?;
                        net::Data::Json(j)
                    }
                    other => net::Data::Text(self.show_value(&other, &SayMods::default())),
                })
            }
            None => None,
        };
        let mut hdrs: Vec<(String, String)> = Vec::new();
        for (k, e) in headers {
            let v = self.eval_expr(e, frame, out)?;
            hdrs.push((k.clone(), self.show_value(&v, &SayMods::default())));
        }
        let mut qs: Vec<(String, String)> = Vec::new();
        for (k, e) in query {
            let v = self.eval_expr(e, frame, out)?;
            qs.push((k.clone(), self.show_value(&v, &SayMods::default())));
        }
        let addr = net::Address {
            secure: address.secure,
            host: address.host.clone(),
            port: address.port,
            path: if address.path.is_empty() {
                "/".to_string()
            } else {
                address.path.clone()
            },
        };
        let req = net::Request {
            method: wire_method(method),
            address: addr,
            data,
            headers: hdrs,
            query: qs,
            skip_tls,
        };
        let resp = net::request(&req).map_err(|_| TErr::Signal)?;
        // the response record (S60): status (whole), body (text),
        // headers (map of text to text). A status of 400 or more is a
        // response, not a failure.
        let record = Value::Record(
            "response".to_string(),
            vec![
                ("status".to_string(), Value::Whole(resp.status as i64)),
                (
                    "body".to_string(),
                    Value::Text(String::from_utf8_lossy(&resp.body).to_string()),
                ),
                (
                    "headers".to_string(),
                    Value::Map(
                        resp.headers
                            .into_iter()
                            .map(|(k, v)| (Value::Text(k), Value::Text(v)))
                            .collect(),
                    ),
                ),
            ],
        );
        frame.last_result = Some(record);
        Ok(Flow::Normal)
    }

    /// The answer one Respond builds (M4-S69).
    #[inline(never)]
    fn build_response(
        &mut self,
        kind: &sem::RespondKind,
        frame: &mut Frame,
        out: &mut String,
    ) -> Result<net::ServerResponse, TErr> {
        let mods = SayMods::default();
        match kind {
            sem::RespondKind::Text(e) => {
                let v = self.eval_expr(e, frame, out)?;
                let body = self.show_value(&v, &mods);
                Ok(plain_response(200, body))
            }
            sem::RespondKind::Json(e) => {
                let v = self.eval_expr(e, frame, out)?;
                let body = crate::formats::json_compact(&v).map_err(|_| TErr::Signal)?;
                Ok(net::ServerResponse {
                    status: 200,
                    content_type: "application/json".to_string(),
                    body: body.into_bytes(),
                    extra_headers: Vec::new(),
                })
            }
            sem::RespondKind::Status(n, text) => {
                let body = match text {
                    Some(e) => {
                        let v = self.eval_expr(e, frame, out)?;
                        self.show_value(&v, &mods)
                    }
                    None => String::new(),
                };
                Ok(plain_response(*n as u16, body))
            }
            sem::RespondKind::Template(name) => {
                // M4-S69: the file NAME.template in the source folder;
                // {name} replaced and made safe for HTML, {raw name}
                // not. The build check (T0172) has looked at the file
                // and its names; here it is filled.
                let path =
                    std::path::Path::new(&self.prog.source_dir).join(format!("{name}.template"));
                let text = std::fs::read_to_string(&path).map_err(|_| TErr::Signal)?;
                let filled = self.fill_template(&text, frame, out)?;
                Ok(plain_response(200, filled))
            }
            sem::RespondKind::Literally(e) => {
                let v = self.eval_expr(e, frame, out)?;
                let body = self.show_value(&v, &mods);
                Ok(plain_response(200, body))
            }
        }
    }

    /// Fill a template: every {name} is the visible name's value shown
    /// as Say would and made safe for HTML; {raw name} is not.
    #[inline(never)]
    fn fill_template(
        &mut self,
        text: &str,
        frame: &mut Frame,
        out: &mut String,
    ) -> Result<String, TErr> {
        let chars: Vec<char> = text.chars().collect();
        let mut result = String::new();
        let mut i = 0;
        let mods = SayMods::default();
        while i < chars.len() {
            if chars[i] == '{' {
                let mut j = i + 1;
                let mut word = String::new();
                while j < chars.len() && chars[j] != '}' && !chars[j].is_whitespace() {
                    word.push(chars[j]);
                    j += 1;
                }
                if j < chars.len() && chars[j] == '}' {
                    if let Some(name) = word.strip_prefix("raw ") {
                        if let Some(v) = frame.find(name) {
                            let v = v.clone();
                            result.push_str(&self.show_value(&v, &mods));
                            i = j + 1;
                            continue;
                        }
                    } else if let Some(v) = frame.find(&word) {
                        let v = v.clone();
                        let shown = self.show_value(&v, &mods);
                        result.push_str(&html_safe(&shown));
                        i = j + 1;
                        continue;
                    }
                }
                result.push('{');
                i += 1;
            } else {
                result.push(chars[i]);
                i += 1;
            }
        }
        Ok(result)
    }

    /// Serve (M4-S64): bind, run the block's ordinary sentences once,
    /// then the accept loop until the program ends or Exit. Each
    /// request runs its handler body inline (the eager task model),
    /// with request and session provided.
    #[inline(never)]
    fn exec_serve(
        &mut self,
        port: u16,
        secure: bool,
        cert: &Option<sem::FileRef>,
        key: &Option<sem::FileRef>,
        body: &[sem::Stmt],
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Flow> {
        // the TLS config first: a certificate the run cannot use fails
        // the Serve sentence (T0619, reported anonymously in this cut).
        // The native runtime builds without TLS (logged): a secure Serve
        // there fails anonymously.
        #[cfg(feature = "tls")]
        let tls_config = if secure {
            let Some(c) = cert else {
                return Err(TErr::Signal);
            };
            let Some(k) = key else {
                return Err(TErr::Signal);
            };
            let cert_path = self.resolve_file(c, frame)?;
            let key_path = self.resolve_file(k, frame)?;
            let refused = || {
                fatal(
                    "T0619",
                    "TLS verification failed.",
                    "Fix the certificate or the address.",
                )
            };
            let cert_pem = std::fs::read(&cert_path).map_err(|_| refused())?;
            let key_pem = std::fs::read(&key_path).map_err(|_| refused())?;
            Some(net::tls_server_config(&cert_pem, &key_pem).map_err(|_| {
                fatal(
                    "T0619",
                    "TLS verification failed.",
                    "Fix the certificate or the address.",
                )
            })?)
        } else {
            None
        };
        #[cfg(not(feature = "tls"))]
        if secure {
            return Err(TErr::Signal);
        }
        #[cfg(not(feature = "tls"))]
        let _ = (&cert, &key);
        // T0618: a port in use fails the Serve sentence.
        let listener = std::net::TcpListener::bind(("0.0.0.0", port))
            .map_err(|_| fatal("T0618", "Serve cannot listen.", "Use another port."))?;
        listener.set_nonblocking(true).map_err(|_| TErr::Signal)?;
        // the block's ordinary sentences run once at start (S64)
        let ordinary: Vec<sem::Stmt> = body
            .iter()
            .filter(|st| {
                !matches!(
                    st,
                    sem::Stmt::WhenSomeone { .. } | sem::Stmt::WhenLive { .. }
                )
            })
            .cloned()
            .collect();
        let flow = self.exec_stmts(&ordinary, frame, out)?;
        match flow {
            Flow::Normal | Flow::Skip => {}
            other => return Ok(other),
        }
        // the accept loop (nonblocking, so the signals stay pollable);
        // the parked live sessions are polled on every pass too
        loop {
            self.tick()?;
            self.poll_signals(frame, out)?;
            match listener.accept() {
                Ok((tcp, _)) => {
                    let _ = tcp.set_nodelay(true);
                    tcp.set_nonblocking(false).ok();
                    #[cfg(feature = "tls")]
                    let mut conn = match &tls_config {
                        Some(cfg) => net::tls_accept(cfg, tcp),
                        None => net::ServerConn::Plain(tcp),
                    };
                    #[cfg(not(feature = "tls"))]
                    let mut conn = net::ServerConn::Plain(tcp);
                    // one idle read minute; the loop keeps serving after
                    conn.set_timeouts(Some(std::time::Duration::from_secs(60)));
                    self.serve_one_connection(conn, body, secure, frame, out)?;
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
                Err(_) => {}
            }
            // M4-S73/D13 (route A): every parked live session gets one
            // non-blocking read attempt per pass; the ready ones resume.
            self.poll_live_sessions(frame, out)?;
            std::thread::sleep(std::time::Duration::from_millis(25));
        }
    }

    /// One connection: read a request, dispatch it to the matching
    /// handler, write the answer (M4-S66/S71/S73).
    #[inline(never)]
    fn serve_one_connection(
        &mut self,
        mut conn: net::ServerConn,
        handlers: &[sem::Stmt],
        secure: bool,
        frame: &mut Frame,
        out: &mut String,
    ) -> R<()> {
        // M4-S74: HTTP/1.1 keep-alive is the default, so one connection
        // serves requests until the client closes or asks to close.
        // `pending` carries bytes of a request that arrived early.
        let mut pending: Vec<u8> = Vec::new();
        loop {
            let read_result =
                net::read_server_request_buffered(&mut pending, &mut |buf| conn.read(buf));
            let req = match read_result {
                Ok(Some(r)) => r,
                Ok(None) => return Ok(()), // the client went away
                Err(e) => {
                    // the 413/431 limit statuses (S70); anything else is a
                    // dead connection - both keep the server running
                    let status = if e.message == "413" {
                        413
                    } else if e.message == "431" {
                        431
                    } else {
                        return Ok(());
                    };
                    let _ = net::write_server_response(
                        &mut |buf| conn.write(buf),
                        &net::ServerResponse {
                            status,
                            content_type: "text/plain; charset=utf-8".to_string(),
                            body: Vec::new(),
                            extra_headers: Vec::new(),
                        },
                    );
                    return Ok(());
                }
            };
            let keep_alive = !req
                .headers
                .iter()
                .any(|(k, v)| k == "connection" && v.eq_ignore_ascii_case("close"));
            // the WebSocket pages first (S73): a live upgrade skips the
            // ordinary request path
            if net::is_ws_upgrade(&req.method, &req.headers) {
                for h in handlers {
                    if let sem::Stmt::WhenLive {
                        page,
                        pattern,
                        body,
                        ..
                    } = h
                    {
                        if let Some(params) = match_pattern(pattern, &req.segments) {
                            // M4-S73/D13: the body becomes a parked session
                            // the accept loop polls; it never blocks here
                            return self.live_session_start(
                                conn,
                                &req.headers,
                                page,
                                params,
                                body,
                                frame,
                                out,
                            );
                        }
                    }
                }
                let _ =
                    net::write_server_response(&mut |buf| conn.write(buf), &not_found_response());
                return Ok(());
            }
            // the page NAME that matched + the parameters
            let mut matched: Option<(&String, Vec<(String, String)>, &Vec<sem::Stmt>)> = None;
            for h in handlers {
                if let sem::Stmt::WhenSomeone {
                    method,
                    page,
                    pattern,
                    body,
                    ..
                } = h
                {
                    if method.wire() != req.method {
                        continue;
                    }
                    if let Some(params) = match_pattern(pattern, &req.segments) {
                        matched = Some((page, params, body));
                        break;
                    }
                }
            }
            let Some((page, params, body)) = matched else {
                // S71: a request that matches no handler gets 404 not found
                let _ = net::write_server_response_keep(
                    &mut |buf| conn.write(buf),
                    &not_found_response(),
                    keep_alive,
                );
                if keep_alive {
                    continue;
                }
                return Ok(());
            };
            // the session (S72): looked up by the cookie; a new one rides
            // home as Set-Cookie lykaon_session=... (HttpOnly, SameSite=Lax,
            // Secure when TLS). The 30-minute-expiry purge runs here too.
            let cookie = req
                .headers
                .iter()
                .find(|(k, _)| k == "cookie")
                .and_then(|(_, v)| {
                    v.split(';').find_map(|c| {
                        c.trim()
                            .strip_prefix("lykaon_session=")
                            .map(|s| s.to_string())
                    })
                });
            let (session_value, session_cookie) = self.take_session(cookie.clone());
            // the handler body runs with request and session provided
            // (M4-S68); the eager model runs it inline on this thread
            frame.push();
            frame.define("session", session_value.clone());
            self.handler_ctx = Some(HandlerCtx {
                method: req.method.clone(),
                page: page.clone(),
                params,
                query: req.query.clone(),
                headers: req.headers.clone(),
                body: req.body.clone(),
                session: session_value.clone(),
                cookie: session_cookie.clone(),
                session_new: cookie.is_none(),
                response: None,
                ws: None,
            });
            let result = self.exec_stmts(body, frame, out);
            let ctx = self.handler_ctx.take();
            // the session map goes back into the server's store: the body's
            // Put/Remove changed the frame's own map (a value copy), so the
            // final map is read back from the frame, not from the ctx
            let session_final = frame.find("session").cloned().unwrap_or_else(|| {
                ctx.as_ref()
                    .map(|c| c.session.clone())
                    .unwrap_or_else(|| session_value.clone())
            });
            let scope = frame.pop();
            if let Some(scope) = scope {
                let _ = self.run_cleanups(scope, out);
            }
            self.put_session(&session_cookie, session_final);
            // the answer: the stashed response, or 500 internal error
            // (M4-D15) when the handler failed or stopped without one
            let mut resp = match (&result, ctx.as_ref().and_then(|c| c.response.clone())) {
                (_, Some(r)) => r,
                (Ok(_), None) => {
                    // the body ended without Respond (T0166's dynamic twin)
                    self.log_handler_failure(out, "the handler ended without Respond.");
                    internal_error_response()
                }
                (Err(TErr::Exit(code)), None) => {
                    // M4-S64: the program ends (Exit ends the server too);
                    // no answer goes out
                    return Err(TErr::Exit(*code));
                }
                (Err(_), None) => {
                    // M4-D15: 500 and the body internal error, the failure
                    // in the log at level error (S71); the server keeps
                    // running
                    self.log_handler_failure(out, "the handler failed.");
                    internal_error_response()
                }
            };
            // the Set-Cookie ride-home (S72) when the session is new
            if cookie.is_none() {
                let mut sc =
                    format!("lykaon_session={session_cookie}; Path=/; HttpOnly; SameSite=Lax");
                if secure {
                    sc.push_str("; Secure");
                }
                resp.extra_headers.push(("Set-Cookie".to_string(), sc));
            }
            let _ = net::write_server_response_keep(&mut |buf| conn.write(buf), &resp, keep_alive);
            if keep_alive {
                continue;
            }
            return Ok(());
        }
    }

    /// The live connection (S73, M4-D13 route A): the 101 handshake,
    /// then the body becomes a parked session the accept loop polls.
    /// `connection` is bound as a real connection value in the session's
    /// own scope, so a body can store it in a list and broadcast.
    #[inline(never)]
    #[allow(clippy::too_many_arguments)]
    fn live_session_start(
        &mut self,
        mut conn: net::ServerConn,
        headers: &[(String, String)],
        page: &str,
        params: Vec<(String, String)>,
        body: &[sem::Stmt],
        frame: &mut Frame,
        out: &mut String,
    ) -> R<()> {
        let Ok(handshake) = net::ws_handshake_response(headers) else {
            return Ok(()); // a broken upgrade: the connection just ends
        };
        // the session reads and writes without blocking: the accept
        // loop polls every parked session on every pass (M4-D13 route A)
        conn.set_nonblocking(true);
        let ws = std::rc::Rc::new(std::cell::RefCell::new(net::WsStream { conn }));
        {
            let mut w = ws.borrow_mut();
            if w.conn.write(handshake.as_bytes()).is_err() || w.conn.flush().is_err() {
                return Ok(());
            }
        }
        let id = self.next_conn;
        self.next_conn += 1;
        let (mir, entry) = mir::build_stmts(body);
        let mut st = sem::GenState::default();
        st.started = true;
        st.block = entry;
        st.gcounters = vec![(0, 0); mir.counter_count];
        st.bounds_set = vec![false; mir.counter_count];
        let mut session = LiveSession {
            id,
            conn: ws.clone(),
            pending: Vec::new(),
            closed: false,
            mir: std::sync::Arc::new(mir),
            entry,
            st,
            page: page.to_string(),
            params,
            scopes: Vec::new(),
            base_depth: frame.scopes.len(),
        };
        // M4-S73: the provided connection is a REAL value: the session's
        // own base scope holds it (a copy kind, storable in lists and
        // maps), so a body can Add it to a list and Send to the copies.
        frame.push();
        frame.define("connection", Value::Conn(id));
        // the session registers BEFORE its first pass: its own Send and
        // Receive resolve the socket through the live table
        self.live.push(session);
        // the first pass runs now (it usually parks at the first
        // Receive); the accept loop owns the session from here on
        let alive = self.run_live_session(id, frame, out)?;
        if !alive {
            if let Some(idx) = self.live.iter().position(|s| s.id == id) {
                self.live.remove(idx);
            }
        }
        Ok(())
    }

    /// One pass of the live session `id`: the frozen scopes go back on
    /// the server frame, the body runs from its parked pc until the next
    /// park or its end, and the scopes freeze again (or the cleanups
    /// run). False = the session ended (or failed): the caller drops it.
    /// The session stays in the live table the whole time: its own
    /// sentences and the other sessions' sentences resolve connections
    /// through the table.
    fn run_live_session(&mut self, id: u64, frame: &mut Frame, out: &mut String) -> R<bool> {
        self.end_session = false;
        self.park_conn = false;
        let (page, params, base_depth) = {
            let e = self
                .live
                .iter()
                .find(|s| s.id == id)
                .expect("the session is registered");
            (e.page.clone(), e.params.clone(), e.base_depth)
        };
        let scopes = {
            let e = self
                .live
                .iter_mut()
                .find(|s| s.id == id)
                .expect("the session is registered");
            std::mem::take(&mut e.scopes)
        };
        for sc in scopes.into_iter() {
            frame.scopes.push(sc);
        }
        // the request rows of a live block read through the ambient
        // context (method/page of request and the path parameters)
        self.handler_ctx = Some(HandlerCtx {
            method: "GET".to_string(),
            page,
            params,
            query: Vec::new(),
            headers: Vec::new(),
            body: Vec::new(),
            session: Value::Map(Vec::new()),
            cookie: String::new(),
            session_new: false,
            response: None,
            ws: None,
        });
        self.active_conn = Some(id);
        // a session body never hands back; the handle only carries the
        // mir and a cache the stray-Hand branch can touch
        let (mir, entry) = {
            let e = self
                .live
                .iter()
                .find(|s| s.id == id)
                .expect("the session is registered");
            (e.mir.clone(), e.entry)
        };
        let handle = sem::GeneratorHandle::new(
            String::new(),
            Vec::new(),
            std::sync::Arc::new(std::sync::Mutex::new(Vec::new())),
            std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false)),
            mir.clone(),
            entry,
            Vec::new(),
        );
        // the resumable state runs outside the table and goes back after
        let mut st = {
            let e = self
                .live
                .iter_mut()
                .find(|s| s.id == id)
                .expect("the session is registered");
            std::mem::take(&mut e.st)
        };
        let outcome = self.gen_exec(Some(&handle), &mir, &mut st, frame, out);
        {
            let e = self
                .live
                .iter_mut()
                .find(|s| s.id == id)
                .expect("the session is registered");
            e.st = st;
        }
        self.active_conn = None;
        let ctx = self.handler_ctx.take();
        let _ = ctx;
        // the session's own scopes freeze back off the server frame
        let mut scopes: Vec<ScopeFrame> = Vec::new();
        while frame.scopes.len() > base_depth {
            scopes.insert(0, frame.scopes.pop().unwrap_or_default());
        }
        {
            let e = self
                .live
                .iter_mut()
                .find(|s| s.id == id)
                .expect("the session is registered");
            e.scopes = scopes;
        }
        match outcome {
            // parked: the pc sits on the Receive; resume there later
            Ok(GHold::Parked) => Ok(true),
            // the body ended (or stopped, or observed a close): the
            // cleanups of every scope the session still holds run now
            Ok(_) => {
                let leftover = {
                    let e = self
                        .live
                        .iter_mut()
                        .find(|s| s.id == id)
                        .expect("the session is registered");
                    std::mem::take(&mut e.scopes)
                };
                for sc in leftover.into_iter().rev() {
                    let _ = self.run_cleanups(sc, out);
                }
                Ok(false)
            }
            Err(e) => {
                let leftover = {
                    let e = self
                        .live
                        .iter_mut()
                        .find(|s| s.id == id)
                        .expect("the session is registered");
                    std::mem::take(&mut e.scopes)
                };
                for sc in leftover.into_iter().rev() {
                    let _ = self.run_cleanups(sc, out);
                }
                match e {
                    // M4-S64: Exit ends the program (and the server)
                    TErr::Exit(code) => Err(TErr::Exit(code)),
                    // M4-D15's posture: a failing live block logs at
                    // error level and the server keeps running
                    _ => {
                        self.log_handler_failure(out, "the live block failed.");
                        Ok(false)
                    }
                }
            }
        }
    }

    /// Poll every parked live session (M4-S73/D13 route A): one
    /// non-blocking read per connection answers whether the session can
    /// make progress; the ready ones resume this pass. A session that
    /// no longer lives is dropped.
    fn poll_live_sessions(&mut self, frame: &mut Frame, out: &mut String) -> R<()> {
        if self.live.is_empty() {
            return Ok(());
        }
        let mut ready: Vec<u64> = Vec::new();
        for s in self.live.iter_mut() {
            if s.closed {
                // the peer is gone: the session resumes to observe it
                // (its next Receive answers missing and it ends)
                ready.push(s.id);
                continue;
            }
            // a complete frame already in the pending buffer counts as
            // readable (leftovers of an earlier chunk read)
            let buffered = matches!(net::ws_frame_total(&s.pending), Ok(Some(total)) if s.pending.len() >= total);
            if buffered {
                ready.push(s.id);
                continue;
            }
            let mut w = s.conn.borrow_mut();
            let mut chunk = [0u8; 4096];
            match w.conn.read(&mut chunk) {
                Ok(0) => {
                    s.closed = true;
                    ready.push(s.id);
                }
                Ok(n) => {
                    s.pending.extend_from_slice(&chunk[..n]);
                    ready.push(s.id);
                }
                Err(e) if e.kind == "timed out" => {} // nothing yet
                Err(_) => {
                    s.closed = true;
                    ready.push(s.id);
                }
            }
        }
        for id in ready {
            if !self.live.iter().any(|s| s.id == id) {
                continue;
            }
            let alive = self.run_live_session(id, frame, out)?;
            if !alive {
                if let Some(idx) = self.live.iter().position(|s| s.id == id) {
                    self.live.remove(idx);
                }
            }
        }
        Ok(())
    }

    /// Write one text frame to live connection `id` (M4-S73). A send to
    /// a connection whose block has ended or whose peer closed is
    /// silently dropped: one client's drop must not kill the others'
    /// broadcast (deviation logged).
    fn live_send(&mut self, id: u64, text: &str) -> R<()> {
        let Some(s) = self.live.iter().find(|s| s.id == id) else {
            return Ok(()); // the connection's block has ended
        };
        if s.closed {
            return Ok(());
        }
        let conn = s.conn.clone();
        let frame_data = net::ws_server_frame(text.as_bytes());
        let failed = {
            let mut w = conn.borrow_mut();
            w.conn.write(&frame_data).is_err() || w.conn.flush().is_err()
        };
        if failed {
            // a broken write ends the connection; its own session
            // observes the close at its next Receive
            if let Some(s) = self.live.iter_mut().find(|s| s.id == id) {
                s.closed = true;
            }
        }
        Ok(())
    }

    /// One non-blocking read of live connection `id` (M4-S73): a text
    /// frame is its text (the value is it), a close is missing (and the
    /// session ends after the statement that observed it), and no frame
    /// yet answers None - the caller parks the session at the Receive,
    /// which re-runs on resume.
    fn live_recv(&mut self, id: u64) -> R<Option<Value>> {
        let (conn, mut pending) = {
            let Some(entry) = self.live.iter_mut().find(|s| s.id == id) else {
                // the connection's block has ended: reading from it is
                // missing, and this session ends too (S73)
                self.end_session = true;
                return Ok(Some(Value::Missing));
            };
            if entry.closed {
                // the peer is already known gone: missing, session ends
                self.end_session = true;
                return Ok(Some(Value::Missing));
            }
            (entry.conn.clone(), std::mem::take(&mut entry.pending))
        };
        let read_result = {
            let mut w = conn.borrow_mut();
            net::ws_read_frame_buffered(&mut pending, &mut |buf| w.conn.read(buf))
        };
        if let Some(entry) = self.live.iter_mut().find(|s| s.id == id) {
            entry.pending = pending;
        }
        let observe_close = |me: &mut Self| {
            if let Some(s) = me.live.iter_mut().find(|s| s.id == id) {
                s.closed = true;
            }
            me.end_session = true;
        };
        match read_result {
            Ok(Some((1, payload))) => match String::from_utf8(payload) {
                Ok(t) => Ok(Some(Value::Text(t))),
                Err(_) => Err(TErr::Signal),
            },
            Ok(Some(_)) => Ok(Some(Value::Missing)), // a non-text frame
            Ok(None) => {
                // the close frame: missing, and the session ends (S73)
                observe_close(self);
                Ok(Some(Value::Missing))
            }
            Err(e) if e.kind == "closed" => {
                observe_close(self);
                Ok(Some(Value::Missing))
            }
            Err(e) if e.kind == "busy" => {
                // no frame yet: the session parks at this Receive
                self.park_conn = true;
                Ok(None)
            }
            Err(_) => Err(TErr::Signal), // a bad frame fails the block
        }
    }

    /// The server's session store: an in-memory map from the cookie
    /// value to the session map, purged of the 30-minute-expired
    /// entries on every look-up (S72; sessions are lost on restart).
    fn take_session(&mut self, cookie: Option<String>) -> (Value, String) {
        let now = std::time::SystemTime::now();
        self.sessions.retain(|_, (_, seen)| {
            now.duration_since(*seen)
                .map(|d| d.as_secs() < 1800)
                .unwrap_or(false)
        });
        match cookie {
            Some(c) if self.sessions.contains_key(&c) => {
                let (v, seen) = self
                    .sessions
                    .get(&c)
                    .cloned()
                    .unwrap_or((Value::Map(Vec::new()), now));
                self.sessions.insert(c.clone(), (v.clone(), now));
                (v, c)
            }
            _ => {
                let c = random_cookie_value();
                let v = Value::Map(Vec::new());
                self.sessions.insert(c.clone(), (v.clone(), now));
                (v, c)
            }
        }
    }

    fn put_session(&mut self, cookie: &str, session: Value) {
        let now = std::time::SystemTime::now();
        self.sessions.insert(cookie.to_string(), (session, now));
    }

    /// The error-level log line of a handler failure (M4-D15/S71).
    #[inline(never)]
    fn log_handler_failure(&mut self, out: &mut String, what: &str) {
        let start = out.len();
        out.push_str("error ");
        out.push_str(what);
        out.push('\n');
        self.err_ranges.push((start, out.len()));
    }

    fn poll_signals(&mut self, frame: &mut Frame, out: &mut String) -> R<()> {
        use crate::signals as sig;
        let arrivals = [
            (sem::SignalName::Interrupt, sig::take_interrupt()),
            (sem::SignalName::Stop, sig::take_stop()),
            (sem::SignalName::Hangup, sig::take_hangup()),
        ];
        for (name, fired) in arrivals {
            if !fired {
                continue;
            }
            if let Some((_, body)) = self.signal_handlers.iter().find(|(s, _)| *s == name) {
                let body = body.clone();
                frame.push();
                let flow = self.exec_stmts(&body, frame, out);
                let _ = self.run_cleanups(frame.pop().unwrap_or_default(), out);
                match flow {
                    // the block's Give back lands in it (a task's result
                    // shape, kept where a later sentence can read it)
                    Ok(Flow::Back(v, _)) | Ok(Flow::Hand(v)) => {
                        frame.last_result = Some(v);
                    }
                    Ok(Flow::Normal) | Ok(Flow::Skip) | Ok(Flow::Stop) => {}
                    Err(e) => return Err(e),
                }
            } else {
                while let Some(scope) = frame.pop() {
                    let _ = self.run_cleanups(scope, out);
                }
                return Err(TErr::Exit(name.default_exit()));
            }
        }
        Ok(())
    }

    fn exec_stmts(&mut self, stmts: &[sem::Stmt], frame: &mut Frame, out: &mut String) -> R<Flow> {
        for st in stmts {
            self.tick()?;
            match self.exec_stmt(st, frame, out)? {
                Flow::Normal => {}
                Flow::Hand(v) => {
                    if self.in_generator {
                        // A generator body captures each Hand back and keeps
                        // running; the run ends when the body ends (ch.25).
                        self.pending_hands.push(v);
                        continue;
                    }
                    return Ok(Flow::Hand(v));
                }
                other => return Ok(other),
            }
            // Only Combine/Apply give a result for it/them (Ch.16); every
            // other sentence clears the pronoun reference. Wait for is an
            // M4 exception: the result is it (M4-S4). Receive from is one
            // too: it is the received value (M4-S13). Spread is one for
            // them: the item-ordered results (M4-S23).
            if !matches!(
                st,
                sem::Stmt::Evaluate { .. }
                    | sem::Stmt::WaitFor { .. }
                    | sem::Stmt::Receive { .. }
                    | sem::Stmt::Spread { .. }
                    // M4 (7.5): the read-ish file sentences leave their
                    // result in it too (a read line also sets it)
                    | sem::Stmt::ReadFile { .. }
                    | sem::Stmt::ReadBytes { .. }
                    | sem::Stmt::ListFolder { .. }
                    // M4-6 (7.6): the decoded value of a format read
                    | sem::Stmt::ReadFormat { .. }
                    | sem::Stmt::ReadFormatText { .. }
                    // M4-8: the child's standard output (M4-D16) and the
                    // input line read this round (M4-S85)
                    | sem::Stmt::RunProc { .. }
                    | sem::Stmt::ForEachInput { .. }
                    // M4-10: the response record is it; a received live
                    // frame is it too
                    | sem::Stmt::Fetch { .. }
                    | sem::Stmt::PostTo { .. }
                    | sem::Stmt::WsRecv { .. }
            ) {
                frame.last_result = None;
            }
            // M4-S79: the signals are polled at the boundary after each
            // sentence (a superset of the pause list, so an arrival cannot
            // sit waiting behind a non-pausing stretch - logged). After the
            // sentence, so a block registered by the sentence just run
            // answers an arrival that happened before it.
            self.poll_signals(frame, out)?;
        }
        Ok(Flow::Normal)
    }

    /// M4 (Appendix K 7.4): sleep until `end`, running due timer rounds on
    /// the way: a repeating Every runs its block at each fixed-rate round
    /// start (M4-D12; rounds never overlap because there is one worker in
    /// this cut, and a round that runs long starts the next at once); an
    /// After fires once at/after its deadline. Stop. inside a round ends
    /// that Every (M4-S26). While a round is running, a nested drive does
    /// nothing (re-entrancy guard; logged).
    fn drive_timers_until(
        &mut self,
        end: std::time::Instant,
        frame: &mut Frame,
        out: &mut String,
    ) -> R<()> {
        loop {
            let now = std::time::Instant::now();
            // The earliest due round fires FIRST, even when the clock
            // already passed `end` (a sleep can overshoot the window, and
            // an event that reached its deadline inside the window must
            // still fire - firing is the progress step that ends every
            // loop here).
            let idx = frame.timers.iter().position(|t| {
                (t.every && !t.stopped && t.next_round <= now)
                    || (!t.every && !t.done && t.deadline <= now)
            });
            let Some(i) = idx else {
                // M4-G47: due watcher polls fire on the same beat, and
                // before the window check, exactly like timer events (a
                // fired poll keeps the loop moving)
                if self.poll_watchers(frame, out)? {
                    continue;
                }
                // nothing due: wait until the next event or the window end
                if now >= end {
                    return Ok(());
                }
                let mut wake = end;
                for t in &frame.timers {
                    if t.every && !t.stopped && t.next_round < wake {
                        wake = t.next_round;
                    }
                    if !t.every && !t.done && t.deadline < wake {
                        wake = t.deadline;
                    }
                }
                // the next watcher poll beat is a wake as well
                for w in &frame.watchers {
                    if w.stopped {
                        continue;
                    }
                    let next = w.last_poll + WATCH_POLL;
                    if next < wake {
                        wake = next;
                    }
                }
                if wake > now {
                    std::thread::sleep(wake - now);
                }
                continue;
            };
            if self.timer_firing > 0 {
                // nested calendars do not drive (deviation logged)
                return Ok(());
            }
            let body = std::rc::Rc::clone(&frame.timers[i].body);
            let is_every = frame.timers[i].every;
            {
                let t = &mut frame.timers[i];
                if t.every {
                    // fixed rate: the next round starts interval after
                    // the START of this round (M4-D12)
                    t.next_round = t.next_round + t.interval;
                } else {
                    t.done = true;
                }
            };
            frame.push();
            self.timer_firing += 1;
            let flow = self.exec_stmts(&body, frame, out);
            self.timer_firing -= 1;
            let _ = self.run_cleanups(frame.pop().unwrap_or_default(), out);
            match flow {
                Ok(Flow::Stop) if is_every => {
                    // Stop. inside a round ends the timer (M4-S26)
                    if let Some(t) = frame.timers.get_mut(i) {
                        t.stopped = true;
                    }
                }
                Ok(_) => {}
                // a failure in a round propagates: the sleep the main
                // flow was inside is where it surfaces (honest, and the
                // failure stops the rest of the rounds)
                Err(TErr::Signal) | Err(TErr::Yield(_)) | Err(TErr::Fatal(_)) => {
                    return flow.map(|_| ());
                }
                // M4-8: Exit (or a handlerless signal) inside a round ends
                // the program with its code the same way
                Err(e @ TErr::Exit(_)) => return Err(e),
            }
        }
    }

    /// M4-G47: poll every watcher once on the beat. A watcher whose
    /// observed state changed fires its body once per poll (changes
    /// closer than 100 milliseconds merge into one firing, M4-S39); a
    /// Stop. inside the body cancels the watcher; a failure propagates
    /// out of the Sleep the main flow was inside, like a timer round.
    /// Returns whether any poll fired (the caller keeps the loop moving).
    fn poll_watchers(&mut self, frame: &mut Frame, out: &mut String) -> R<bool> {
        if self.timer_firing > 0 {
            // nested calendars do not drive (same re-entrancy guard as
            // the timers)
            return Ok(false);
        }
        let now = std::time::Instant::now();
        let mut fired_any = false;
        for wi in 0..frame.watchers.len() {
            if frame.watchers[wi].stopped || frame.watchers[wi].last_poll + WATCH_POLL > now {
                continue;
            }
            let snapshot = {
                let w = &frame.watchers[wi];
                self.watcher_snapshot(&w.file, frame)
            };
            frame.watchers[wi].last_poll = now;
            if Some(snapshot) == frame.watchers[wi].state {
                continue;
            }
            let body = std::rc::Rc::clone(&frame.watchers[wi].body);
            frame.watchers[wi].state = Some(snapshot);
            frame.push();
            self.timer_firing += 1;
            let flow = self.exec_stmts(&body, frame, out);
            self.timer_firing -= 1;
            let _ = self.run_cleanups(frame.pop().unwrap_or_default(), out);
            match flow {
                Ok(Flow::Stop) => {
                    // Stop. ends this watcher (choice logged)
                    frame.watchers[wi].stopped = true;
                    fired_any = true;
                }
                Ok(_) => fired_any = true,
                Err(_) => return flow.map(|_| true),
            }
        }
        Ok(fired_any)
    }

    /// The observed state of one watched path: (exists, mtime, size).
    /// A deletion is a change too (a delete event fires the block,
    /// M4-S39); a rename is seen as the delete-and-create pair it is.
    /// A path that does not resolve reads as absent.
    fn watcher_snapshot(
        &self,
        f: &sem::FileRef,
        frame: &Frame,
    ) -> (bool, Option<std::time::SystemTime>, u64) {
        let path = match self.resolve_file(f, frame) {
            Ok(p) => p,
            Err(_) => return (false, None, 0),
        };
        match std::fs::metadata(&path) {
            Ok(m) => (true, m.modified().ok(), m.len()),
            Err(_) => (false, None, 0),
        }
    }

    /// M4-S29..S32: resolve a file or folder reference to a concrete
    /// path. A temporary binding (Make temporary file NAME.) wins over
    /// the literal reading of the name (choice logged); a `file named`
    /// path is used as written (terminal per the grammar); otherwise
    /// the root chooses the base folder (M4-S30) and the folder steps
    /// join from the file outward (M4-S31: the first named folder is
    /// closest to the file, so they join in reverse text order).
    fn resolve_file(&self, f: &sem::FileRef, frame: &Frame) -> R<std::path::PathBuf> {
        if let Some(t) = &f.temp {
            for sc in frame.scopes.iter().rev() {
                if let Some(v) = sc.vars.get(t.as_str()) {
                    if let Value::Text(p) = v {
                        return Ok(std::path::PathBuf::from(p));
                    }
                }
            }
            // not bound at run time (a Make the run has not reached):
            // the name reads as a plain file name next to the program
            // (leniency, logged)
        }
        if let Some(raw) = &f.raw {
            return Ok(std::path::PathBuf::from(raw));
        }
        // M4-S29: a relative reference starts at the program's own folder
        let mut base = std::path::PathBuf::from(&self.prog.source_dir);
        match &f.root {
            Some(sem::FileRoot::Parent) => {
                base = base.parent().map(|p| p.to_path_buf()).unwrap_or(base);
            }
            Some(sem::FileRoot::Home) => {
                if let Ok(h) = std::env::var("USERPROFILE") {
                    base = std::path::PathBuf::from(h);
                } else if let Ok(h) = std::env::var("HOME") {
                    base = std::path::PathBuf::from(h);
                } else {
                    return Err(TErr::Signal);
                }
            }
            Some(sem::FileRoot::Current) => {
                base = std::env::current_dir().map_err(|_| TErr::Signal)?;
            }
            Some(sem::FileRoot::Temporary) => {
                base = std::env::temp_dir();
            }
            Some(sem::FileRoot::Root) => {
                // "/" on Linux; the root of the current drive like "C:\"
                // on Windows (the Windows reading is logged)
                let base_now = std::env::current_dir().map_err(|_| TErr::Signal)?;
                // the anchor of the current working directory: "/" on
                // Linux, the root of the current drive like "C:\" on
                // Windows (the Windows reading is logged)
                base = match base_now.components().next() {
                    Some(std::path::Component::Prefix(p)) => {
                        let mut s = p.as_os_str().to_string_lossy().to_string();
                        if !s.ends_with('\\') {
                            s.push('\\');
                        }
                        std::path::PathBuf::from(s)
                    }
                    _ => std::path::PathBuf::from("/"),
                };
            }
            Some(sem::FileRoot::Drive(d)) => {
                // M4-S30: `on drive NAME` is for systems that have
                // drives - X:\ here, and a fatal T0171 on Linux
                #[cfg(target_os = "linux")]
                {
                    return Err(fatal(
                        "T0171",
                        "A path uses a drive name on a system without drives.",
                        "Write the path without on drive, or run where drives exist.",
                    ));
                }
                #[cfg(not(target_os = "linux"))]
                {
                    base = std::path::PathBuf::from(format!("{}:\\", d.trim().to_uppercase()));
                }
            }
            None => {}
        }
        // M4-S31: folder steps nest from the file outward (innermost
        // first in text order), so they join in reverse
        for fo in f.folders.iter().rev() {
            if !fo.is_empty() {
                base = base.join(fo);
            }
        }
        if f.ext.is_some() {
            base = base.join(format!("{}.{}", f.name, f.ext.clone().unwrap_or_default()));
        } else if !f.name.is_empty() {
            base = base.join(&f.name);
        }
        Ok(base)
    }

    /// M4-S35: the bytes of a Write/Append/Replace operand: the text is
    /// one line (the text and one line feed); a list writes each item
    /// as its own line (a list of text; values of other kinds take
    /// their shown wording, logged); every other value is one line of
    /// its shown wording.
    fn file_bytes(&mut self, value: &sem::Expr, frame: &mut Frame, out: &mut String) -> R<Vec<u8>> {
        let v = self.eval_expr(value, frame, out)?;
        let empty = SayMods::default();
        let mut buf = String::new();
        match v {
            Value::List(items) => {
                for item in &items {
                    buf.push_str(&self.show_value(item, &empty));
                    buf.push('\n');
                }
            }
            other => {
                buf.push_str(&self.show_value(&other, &empty));
                buf.push('\n');
            }
        }
        Ok(buf.into_bytes())
    }

    /// M4-S28: at main end the program does not end while an After is
    /// still pending in its main scope - the pending one-shot timers fire
    /// here (real sleeps), and the Everies are cancelled with the main
    /// scope (M4-S25/S26). Timers registered BY a round run afterwards are
    /// cancelled with the scope of their registration (snapshot semantics,
    /// deviation logged).
    fn fire_pending_afters(&mut self, frame: &mut Frame, out: &mut String) -> R<()> {
        let start_count = frame.timers.len();
        loop {
            let dl = frame.timers[..start_count]
                .iter()
                .filter(|t| !t.every && !t.done)
                .map(|t| t.deadline)
                .min();
            let Some(dl) = dl else {
                return Ok(());
            };
            self.drive_timers_until(dl + std::time::Duration::from_millis(1), frame, out)?;
        }
    }

    fn exec_stmt(&mut self, st: &sem::Stmt, frame: &mut Frame, out: &mut String) -> R<Flow> {
        match st {
            sem::Stmt::Note => Ok(Flow::Normal),
            // ---- M4 (Appendix K) tasks --------------------------------
            // FIRST-CUT EXECUTION MODEL (deviation logged): a task runs
            // EAGERLY on the starting worker at the Start task sentence;
            // Wait for then takes the stored result. No interleaving and
            // no real worker pool yet - Interp is single-threaded and not
            // Sync; the pool increment will run task bodies on real
            // workers. The sentence grammar, name scoping (M4-D2), the
            // capture checks (T0451) and the result/second-wait rules are
            // in place NOW so the pool increment swaps execution only.
            sem::Stmt::StartTask { name, body } => {
                // (a restarted name overwrites the earlier entry; task-name
                // uniqueness is not pinned by Appendix K in this cut)
                frame.tasks.insert(name.clone(), TaskState::Running);
                frame.push();
                let flow = self.exec_stmts(body, frame, out)?;
                let scope = frame.pop();
                if let Some(scope) = scope {
                    let _ = self.run_cleanups(scope, out);
                }
                let result = match flow {
                    // Give back EXPR. as the task's last sentence (M4-S3);
                    // a failure inside is still a failure of this run.
                    Flow::Back(v, came_from_fail) => {
                        if came_from_fail {
                            return Ok(Flow::Back(v, true));
                        }
                        Some(v)
                    }
                    Flow::Normal | Flow::Skip | Flow::Stop => None,
                    // a Hand back cannot end a task body
                    Flow::Hand(v) => return Ok(Flow::Hand(v)),
                };
                frame.tasks.insert(name.clone(), TaskState::Done(result));
                Ok(Flow::Normal)
            }
            sem::Stmt::WaitFor { name } => {
                // M4-S4: pause until the task ends; the result is taken
                // once (M4-D14) - a copy-kind result is copied and a
                // second wait is allowed; a second wait on a moved-away
                // result is T0334. A task that gave nothing waits to
                // missing, taken once as well.
                if let Some(state) = frame.tasks.get_mut(name) {
                    return match state {
                        TaskState::Taken => Err(fatal(
                            "T0334",
                            "The task result was taken twice.",
                            "Wait for a task once, or name a different task.",
                        )),
                        TaskState::Running => Err(fatal(
                            "T0334",
                            "The task is still running and waits for itself.",
                            "Wait for a task from outside its body.",
                        )),
                        TaskState::Done(None) => {
                            *state = TaskState::Taken;
                            frame.last_result = Some(Value::Missing);
                            Ok(Flow::Normal)
                        }
                        TaskState::Done(Some(v)) if !value_moves(v) => {
                            let v = v.clone();
                            // the result is it (M4-S4)
                            frame.last_result = Some(v);
                            Ok(Flow::Normal)
                        }
                        TaskState::Done(Some(v)) => {
                            let v = v.clone();
                            *state = TaskState::Taken;
                            // the result is it (M4-S4)
                            frame.last_result = Some(v);
                            Ok(Flow::Normal)
                        }
                    };
                }
                // the compiler rejects this with T0168 before it can run
                Err(fatal(
                    "T0168",
                    "Wait for names a name that is not a task.",
                    "Name a task.",
                ))
            }
            sem::Stmt::DoTogether { body } => {
                // M4-S5 first cut: run the block; the tasks inside were
                // started eagerly, so they have all ended; tasks never
                // outlive their block (M4-S6). Real cancellation arrives
                // with the worker pool.
                frame.push();
                let flow = self.exec_stmts(body, frame, out)?;
                let scope = frame.pop();
                if let Some(scope) = scope {
                    let _ = self.run_cleanups(scope, out);
                }
                match flow {
                    Flow::Normal | Flow::Skip | Flow::Stop => Ok(Flow::Normal),
                    Flow::Hand(v) => Ok(Flow::Hand(v)),
                    other => Ok(other),
                }
            }
            sem::Stmt::StopTask { .. } => {
                // M4-S7 first cut: eager tasks have already ended, so a
                // cancel request has nothing left pending to reach. The
                // cancel-request machinery comes with the worker pool.
                Ok(Flow::Normal)
            }
            sem::Stmt::SleepFor { amount, unit } => {
                use std::time::Duration;
                // M4-S9: Sleep for pauses; it is on the pause list. In the
                // eager first cut the sleep ALSO drives the timer calendar
                // (M4-4): due Everies run fixed-rate rounds (M4-D12) and
                // past-deadline Afters run once, real-walled.
                let ms = timer_unit_ms(*amount, unit);
                let end = std::time::Instant::now() + Duration::from_millis(ms);
                self.drive_timers_until(end, frame, out)?;
                Ok(Flow::Normal)
            }
            sem::Stmt::Send { value, name } => {
                // M4-G11: Send VALUE to CHANNELNAME. The value is put on the
                // queue; M4-S11 says Send pauses when the channel is full.
                // In the eager first cut, a pause could never be woken (no
                // message can run while this worker is paused), so a full
                // channel and an empty one are deadlock reports in this
                // cut (T0610 family; deviation logged).
                let v = self.eval_expr(value, frame, out)?;
                let target = frame.find(name).cloned();
                if let Some(Value::Conn(id)) = target {
                    // M4-S73/D13: a Send to a connection value writes one
                    // text frame (the shown wording of the value)
                    let text = self.show_value(&v, &SayMods::default());
                    self.live_send(id, &text)?;
                    return Ok(Flow::Normal);
                }
                let Some(Value::Channel(state)) = target else {
                    // the compiler rejects this with T0460-family wording
                    // before it can run (deviation logged: the reuse)
                    return Err(fatal(
                        "T0168",
                        "Send names a name that is not a channel.",
                        "Define a channel and Send to it.",
                    ));
                };
                let mut st = state.borrow_mut();
                if st.closed {
                    // M4-S14: a Send on a closed channel is a bug and stops
                    // the program (T0609).
                    return Err(fatal(
                        "T0609",
                        "A value was sent on a channel with no receivers.",
                        "Keep the receiver open.",
                    ));
                }
                if st.queue.len() >= st.cap {
                    return Err(fatal(
                        "T0610",
                        "Send pauses forever: the channel is full and nothing can receive.",
                        "Receive from the channel before it fills, or a bigger holding number.",
                    ));
                }
                // M4-D14/12: values sent are moved (move kinds) or copied
                // (copy kinds). First cut: every send copies (see deviations).
                let _ = value_moves(&v);
                st.queue.push(v);
                Ok(Flow::Normal)
            }
            sem::Stmt::Receive { name } => {
                // M4-G12: Receive from CHANNELNAME. The oldest item is
                // taken and it is that value (M4-S13); when the channel is
                // closed and empty the value is missing (S6).
                let target = frame.find(name).cloned();
                if let Some(Value::Conn(id)) = target {
                    // M4-S73/D13: a Receive from a connection value reads
                    // one text frame; no frame yet parks the session here
                    match self.live_recv(id)? {
                        Some(v) => frame.last_result = Some(v),
                        None => {}
                    }
                    return Ok(Flow::Normal);
                }
                let Some(Value::Channel(state)) = target else {
                    return Err(fatal(
                        "T0168",
                        "Receive names a name that is not a channel.",
                        "Define a channel of some kind and Receive from it.",
                    ));
                };
                let v = {
                    let mut st = state.borrow_mut();
                    if st.queue.is_empty() {
                        if st.closed {
                            // closed and empty: the value is missing (M4-S13)
                            Value::Missing
                        } else {
                            // M4-S11: Receive pauses when the channel is
                            // empty. In the eager first cut nothing can
                            // wake the pause, so this is a deadlock report
                            // (T0610 family; deviation logged).
                            return Err(fatal(
                                "T0610",
                                "Receive from pauses forever: the channel is empty and no live task can send.",
                                "Send to the channel before receiving from it.",
                            ));
                        }
                    } else {
                        st.queue.remove(0)
                    }
                };
                // the value is it (M4-S13)
                frame.last_result = Some(v);
                Ok(Flow::Normal)
            }
            sem::Stmt::AtomicAdd { value, name } => {
                // M4-G13: Add VALUE to NAME atomically. - one machine step
                // with sequentially consistent order (M4-S19). A counter's
                // plain `Add V to NAME.` lands here as well (M4-S20).
                let v = unwrap_shared_read(self.eval_expr(value, frame, out)?);
                let n = match &v {
                    Value::Whole(n) => *n,
                    _ => {
                        // atomic values are numbers; a fractional add is
                        // not defined by Appendix K (deviation logged)
                        return Err(fatal(
                            "T0113",
                            "The value added atomically is not a whole number.",
                            "Add a whole number.",
                        ));
                    }
                };
                match frame.find_mut(name) {
                    Some(Value::Atomic(slot)) => *slot = slot.wrapping_add(n),
                    Some(Value::Counter(slot)) => *slot = slot.wrapping_add(n),
                    Some(_) => {
                        // only atomic and counter kinds change this way
                        return Err(fatal(
                            "T0406",
                            "Only an atomic number or a counter changes with Add.",
                            "Define the name as atomic number or counter, or use Set on a Changeable name.",
                        ));
                    }
                    None => {
                        return Err(fatal(
                            "T0205",
                            "Add atomically names a name that is not defined.",
                            "Define the name as atomic number or counter first.",
                        ));
                    }
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::AfterTimer { amount, unit, body } => {
                // M4-G14: After N <unit>. starts a one-shot timer and goes
                // on (M4-S25). The eager cut drives timers off real-clock
                // deadlines at Sleep passes (drive_timers_until); an After
                // that never meets a Sleep fires at main end (M4-S28).
                let ms = timer_unit_ms(*amount, unit);
                frame.timers.push(TimerTask {
                    every: false,
                    body: std::rc::Rc::new(body.clone()),
                    deadline: instant_after(ms),
                    interval: std::time::Duration::ZERO,
                    next_round: std::time::Instant::now(),
                    stopped: false,
                    done: false,
                });
                Ok(Flow::Normal)
            }
            sem::Stmt::EveryTimer { amount, unit, body } => {
                // M4-G15: Every N <unit>. repeats the block at a fixed rate
                // (M4-D12); the first round starts after one interval.
                // Stop. inside a round ends it; it is cancelled with the
                // enclosing scope and at main end (M4-S26).
                let ms = timer_unit_ms(*amount, unit);
                frame.timers.push(TimerTask {
                    every: true,
                    body: std::rc::Rc::new(body.clone()),
                    deadline: std::time::Instant::now(),
                    interval: std::time::Duration::from_millis(ms),
                    next_round: instant_after(ms),
                    stopped: false,
                    done: false,
                });
                Ok(Flow::Normal)
            }
            sem::Stmt::StreamLoop { var, channel, body } => {
                // M4-G16: For each x as they arrive from CHANNEL. In the
                // eager first cut the loop drains the channel: it receives
                // the queued items one by one and ends when the queue is
                // empty (the book's "until the channel closes" maps to
                // drain-empty here; deviation logged - nothing can send
                // while this loop runs in a single-threaded cut). it and x
                // are each received value (M4-S13); Stop. leaves the loop
                // (M4-S27).
                let Some(Value::Channel(state)) = frame.find(channel).cloned() else {
                    // the compiler rejects this with T0168 first; runtime belt
                    return Err(fatal(
                        "T0168",
                        "For each as they arrive names a name that is not a channel.",
                        "Define a channel of some kind and receive from it in the loop.",
                    ));
                };
                loop {
                    self.tick()?;
                    let next = {
                        let mut st = state.borrow_mut();
                        if st.queue.is_empty() {
                            None
                        } else {
                            Some(st.queue.remove(0))
                        }
                    };
                    let Some(v) = next else { break };
                    frame.push();
                    frame.define(var, v.clone());
                    // the value is it too (M4-S13)
                    frame.last_result = Some(v);
                    let flow = self.exec_stmts(body, frame, out);
                    frame.pop();
                    match flow {
                        Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                        // Stop. leaves the loop (M4-S27)
                        Ok(Flow::Stop) => return Ok(Flow::Normal),
                        Ok(Flow::Hand(v)) => {
                            if self.in_generator {
                                self.pending_hands.push(v);
                            } else {
                                return Ok(Flow::Hand(v));
                            }
                        }
                        Ok(f @ Flow::Back(..)) => return Ok(f),
                        Err(e) => return Err(e),
                    }
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::UseWorkers { count } => {
                // M4-S22: sets the worker count for Spread sentences that
                // follow, in this block and inner blocks; the number is
                // 1 to 256.
                if *count < 1 || *count > 256 {
                    return Err(fatal(
                        "T0113",
                        "A worker count must be a whole number from 1 to 256.",
                        "Write Use 4 workers. (a number from 1 to 256).",
                    ));
                }
                if let Some(sc) = frame.scopes.last_mut() {
                    sc.workers = Some(*count as usize);
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::Spread { items, body } => {
                // M4-G18: Spread each of ITEMS over workers. The eager
                // first cut is a sequential round-runner: one virtual
                // worker per item in item order; the worker count is
                // unobservable in this cut (deviation logged). it is the
                // item (M4-S23); the block's Hand back is that item's
                // result; the results collect into them, in item order. A
                // failure inside stops the other workers and is the
                // failure of the Spread sentence (M4-S24).
                let list = match unwrap_shared_read(self.eval_expr(items, frame, out)?) {
                    Value::List(vs) => vs,
                    _ => {
                        return Err(fatal(
                            "T0305",
                            "Spread works on a list, and the value given is not one.",
                            "Spread each of a list of values over workers.",
                        ));
                    }
                };
                let mut results: Vec<Value> = Vec::new();
                for item in list {
                    self.tick()?;
                    // it is the item (M4-S23)
                    frame.last_result = Some(item.clone());
                    frame.push();
                    let flow = self.exec_stmts(body, frame, out);
                    if let Some(scope) = frame.pop() {
                        let _ = self.run_cleanups(scope, out);
                    }
                    match flow {
                        Ok(Flow::Normal) => {
                            // no Give back this round: the item's result is
                            // missing (first-cut leniency, deviation logged)
                            results.push(Value::Missing)
                        }
                        Ok(Flow::Back(v, false)) => results.push(v),
                        // a failure (Back, true), Hand back, Skip or Stop
                        // propagates: the rest of the items do not run
                        // (M4-S24) and the failure is the Spread's failure
                        other => return other,
                    }
                }
                // the results are them, in item order (M4-S23)
                frame.last_result = Some(Value::List(results));
                Ok(Flow::Normal)
            }
            // ---- M4 (Appendix K 7.5) files and paths ------------------
            sem::Stmt::ReadFile { file } => {
                // M4-G34/S36: the whole text into it, line endings kept;
                // a file that is not valid UTF-8 fails (bad format, S33)
                let path = self.resolve_file(file, frame)?;
                let text = std::fs::read_to_string(&path).map_err(|_| TErr::Signal)?;
                frame.last_result = Some(Value::Text(text));
                Ok(Flow::Normal)
            }
            sem::Stmt::ReadBytes { file } => {
                // M4-G35: the bytes of the file as a list of whole numbers
                let path = self.resolve_file(file, frame)?;
                let bytes = std::fs::read(&path).map_err(|_| TErr::Signal)?;
                frame.last_result = Some(Value::List(
                    bytes.into_iter().map(|b| Value::Whole(b as i64)).collect(),
                ));
                Ok(Flow::Normal)
            }
            sem::Stmt::WriteFile { file, value } => {
                // M4-G36/S34: writing over an existing file fails (kind
                // other: the message is "file already exists"); a plain
                // write creates the file. Failures carry the default kind
                // wording of the run (no per-kind text at run time here;
                // logged with the Ask precedent).
                let path = self.resolve_file(file, frame)?;
                if file.temp.is_none() && std::fs::metadata(&path).is_ok() {
                    return Err(TErr::Signal);
                }
                let bytes = self.file_bytes(value, frame, out)?;
                std::fs::write(&path, bytes).map_err(|_| TErr::Signal)?;
                Ok(Flow::Normal)
            }
            sem::Stmt::AppendFile { file, value } => {
                // M4-G37/S34: append creates the file when needed
                let path = self.resolve_file(file, frame)?;
                let bytes = self.file_bytes(value, frame, out)?;
                let mut f = std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&path)
                    .map_err(|_| TErr::Signal)?;
                f.write_all(&bytes).map_err(|_| TErr::Signal)?;
                Ok(Flow::Normal)
            }
            sem::Stmt::ReplaceFile { file, value } => {
                // M4-G38/S34: creates or overwrites, atomically: a sibling
                // temporary file is written first, then renamed over the
                // target (one same-volume rename)
                let path = self.resolve_file(file, frame)?;
                let bytes = self.file_bytes(value, frame, out)?;
                let mut tmp = path.clone();
                let stamp = format!("tmp{}", std::process::id());
                tmp.set_extension(stamp);
                if std::fs::write(&tmp, &bytes)
                    .and_then(|()| std::fs::rename(&tmp, &path))
                    .is_err()
                {
                    let _ = std::fs::remove_file(&tmp);
                    return Err(TErr::Signal);
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::ForEachLine { var, file, body } => {
                // M4-G39/S36: the lines of the file one by one, each
                // without its line ending (LF or CRLF), streamed. Stop.
                // leaves the loop; the var is the line and so is it.
                let path = self.resolve_file(file, frame)?;
                let f = std::fs::File::open(&path).map_err(|_| TErr::Signal)?;
                let mut rdr = std::io::BufReader::new(f);
                let mut line = String::new();
                loop {
                    line.clear();
                    match rdr.read_line(&mut line) {
                        Ok(0) => break,
                        Ok(_) => {}
                        Err(_) => return Err(TErr::Signal),
                    }
                    if line.ends_with('\n') {
                        line.pop();
                        if line.ends_with('\r') {
                            line.pop();
                        }
                    }
                    self.tick()?;
                    frame.last_result = Some(Value::Text(line.clone()));
                    frame.push();
                    frame.define(var.as_str(), Value::Text(line.clone()));
                    let flow = self.exec_stmts(body, frame, out);
                    let _ = self.run_cleanups(frame.pop().unwrap_or_default(), out);
                    match flow {
                        Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                        Ok(Flow::Stop) => break,
                        Ok(Flow::Hand(v)) => {
                            if self.in_generator {
                                self.pending_hands.push(v);
                            } else {
                                return Ok(Flow::Hand(v));
                            }
                        }
                        Ok(f @ Flow::Back(_, _)) => return Ok(f),
                        Err(e) => return Err(e),
                    }
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::MakeFolder { file } => {
                // M4-G40: the folder and its missing parents are made
                let path = self.resolve_file(file, frame)?;
                std::fs::create_dir_all(&path).map_err(|_| TErr::Signal)?;
                Ok(Flow::Normal)
            }
            sem::Stmt::RemovePath { file } => {
                // M4-G41: a file is removed as a file; a folder reference
                // (or any folder) is removed with all its contents (the
                // recursive reading is logged)
                let path = self.resolve_file(file, frame)?;
                match std::fs::symlink_metadata(&path) {
                    Ok(m) if m.is_dir() => {
                        std::fs::remove_dir_all(&path).map_err(|_| TErr::Signal)?
                    }
                    Ok(_) => std::fs::remove_file(&path).map_err(|_| TErr::Signal)?,
                    Err(_) => return Err(TErr::Signal),
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::MovePath { from, to } => {
                // M4-G42: a rename; if that is refused (a different file
                // system, for example) a copy then a remove
                let a = self.resolve_file(from, frame)?;
                let b = self.resolve_file(to, frame)?;
                if std::fs::rename(&a, &b).is_err() {
                    std::fs::copy(&a, &b).map_err(|_| TErr::Signal)?;
                    std::fs::remove_file(&a).map_err(|_| TErr::Signal)?;
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::DuplicatePath { from, to } => {
                // M4-G43: a byte copy; a folder is duplicated with all
                // its contents (recursive, logged)
                let a = self.resolve_file(from, frame)?;
                let b = self.resolve_file(to, frame)?;
                let ok = if std::fs::symlink_metadata(&a)
                    .map(|m| m.is_dir())
                    .unwrap_or(false)
                {
                    copy_dir_all(&a, &b).is_ok()
                } else {
                    std::fs::copy(&a, &b).is_ok()
                };
                if !ok {
                    return Err(TErr::Signal);
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::ListFolder { file } => {
                // M4-G44: the entry names (files and folders both) into
                // it, sorted byte-wise (the sort choice is logged)
                let path = self.resolve_file(file, frame)?;
                let mut names: Vec<String> = Vec::new();
                for entry in std::fs::read_dir(&path).map_err(|_| TErr::Signal)? {
                    match entry {
                        Ok(e) => names.push(e.file_name().to_string_lossy().to_string()),
                        Err(_) => return Err(TErr::Signal),
                    }
                }
                names.sort();
                frame.last_result = Some(Value::List(names.into_iter().map(Value::Text).collect()));
                Ok(Flow::Normal)
            }
            sem::Stmt::MakeTempFile { name } => {
                // M4-G46/S38: a new empty temporary file; its path is a
                // text bound to NAME, and the file (when it still exists)
                // is removed when the block that holds it ends, even
                // after a failure (the deletion runs at clean-up time)
                self.temp_serial += 1;
                let mut path = std::env::temp_dir();
                path.push(format!(
                    "{}_{}_{}.tmp",
                    name.trim().to_string(),
                    std::process::id(),
                    self.temp_serial
                ));
                std::fs::write(&path, b"").map_err(|_| TErr::Signal)?;
                frame.define(
                    name.as_str(),
                    Value::Text(path.to_string_lossy().to_string()),
                );
                if let Some(sc) = frame.scopes.last_mut() {
                    sc.temps.push(path);
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::WhenFileChanges { file, body } => {
                // M4-G47/S39: the block is a task in the enclosing scope;
                // the eager cut polls on the timer calendar (during
                // Sleeps), changes closer than 100 milliseconds merge
                // into one firing, and rounds run in a fresh pushed scope
                // like timer rounds. The body is captured once here.
                let snapshot = self.watcher_snapshot(file, frame);
                frame.watchers.push(WatcherTask {
                    file: file.clone(),
                    body: std::rc::Rc::new(body.clone()),
                    state: Some(snapshot),
                    last_poll: std::time::Instant::now(),
                    stopped: false,
                });
                Ok(Flow::Normal)
            }
            sem::Stmt::ZipOp { op, from, to } => {
                // M4-G48/S41: zip is reproducible (entries sorted, one
                // fixed first-day-of-1980 stamp, deflate); unzip reads
                // the archive back; gzip writes one gzip stream. All
                // failures are the ordinary run-time can fail wording
                // this cut (logged).
                match op {
                    sem::ZipKind::Zip => {
                        let src = self.resolve_file(from, frame)?;
                        let dst = self.resolve_file(to, frame)?;
                        write_zip(&src, &dst).map_err(|_| TErr::Signal)?;
                        Ok(Flow::Normal)
                    }
                    sem::ZipKind::Unzip => {
                        let src = self.resolve_file(from, frame)?;
                        let dst = self.resolve_file(to, frame)?;
                        unzip_archive(&src, &dst).map_err(|_| TErr::Signal)?;
                        Ok(Flow::Normal)
                    }
                    sem::ZipKind::Gzip => {
                        let src = self.resolve_file(from, frame)?;
                        let dst = self.resolve_file(to, frame)?;
                        let raw = std::fs::read(&src).map_err(|_| TErr::Signal)?;
                        let mut enc = flate2::write::GzEncoder::new(
                            Vec::new(),
                            flate2::Compression::default(),
                        );
                        enc.write_all(&raw).map_err(|_| TErr::Signal)?;
                        let gz = enc.finish().map_err(|_| TErr::Signal)?;
                        std::fs::write(&dst, gz).map_err(|_| TErr::Signal)?;
                        Ok(Flow::Normal)
                    }
                }
            }
            // ---- M4-6 (Appendix K 7.6): the format sentences ----------
            sem::Stmt::ReadFormat {
                format,
                file,
                target,
            } => {
                // M4-S42: the decoded value lands in the fresh result
                // (it). A bad format (a shape the target kind does not
                // hold) fails like the other file sentences: the
                // ordinary anonymous run-time failure (deviation logged;
                // the doc's per-part message needs diagnostics).
                let path = self.resolve_file(file, frame)?;
                let text = std::fs::read_to_string(&path).map_err(|_| TErr::Signal)?;
                let v = crate::formats::decode_format(format, &text, target)
                    .map_err(|_| TErr::Signal)?;
                frame.last_result = Some(v);
                Ok(Flow::Normal)
            }
            sem::Stmt::ReadFormatText {
                format,
                value,
                target,
            } => {
                // M4-6: the decode source is a text value instead of a
                // file; the same typed decode and failure shape.
                let v = self.eval_expr(value, frame, out)?;
                let Value::Text(text) = v else {
                    return Err(TErr::Signal);
                };
                let v = crate::formats::decode_format(format, &text, target)
                    .map_err(|_| TErr::Signal)?;
                frame.last_result = Some(v);
                Ok(Flow::Normal)
            }
            sem::Stmt::SaveFormat {
                value,
                format,
                file,
            } => {
                // M4-S46: json saves pretty with two spaces of
                // indentation and a line feed at the end; the other
                // formats write their doc shapes. Save creates the file
                // and overwrites (the settings-file reading: a program
                // re-saves its settings; logged - the Write sentence's
                // refusal owns only the Write/Append/Replace wording).
                let v = self.eval_expr(value, frame, out)?;
                let mut text = crate::formats::encode_format(format, &v, format == "json")
                    .map_err(|_| TErr::Signal)?;
                if format == "json" {
                    text.push('\n');
                }
                let path = self.resolve_file(file, frame)?;
                std::fs::write(&path, text.as_bytes()).map_err(|_| TErr::Signal)?;
                Ok(Flow::Normal)
            }
            // ---- M4-7 (Appendix K 7.7): random seed --------------------
            sem::Stmt::UseSeed { seed } => {
                // M4-G58: Use seed N. sets the program's generator,
                // xoshiro256++ seeded by splitmix64 from the number.
                self.rng = Some(crate::time4::xoshiro_seed(*seed));
                Ok(Flow::Normal)
            }
            // ---- M4-8 (Appendix K 7.10/7.11): system, tools ------------
            sem::Stmt::RunProc { name, args } => {
                // M4-S76: the program found on the path (the compile check
                // refused a name with a path), one argument per operand,
                // no shell. Run is a pause point (the pause list) - a
                // no-op in the eager cut. The child's standard output is
                // the fresh result (it, M4-D16).
                let mut cmd = std::process::Command::new(name);
                for a in args {
                    let v = self.eval_expr(a, frame, out)?;
                    let empty = SayMods::default();
                    cmd.arg(self.show_value(&v, &empty));
                }
                let done = cmd.output().map_err(|_| TErr::Signal)?;
                frame.last_result = Some(Value::Text(
                    String::from_utf8_lossy(&done.stdout).to_string(),
                ));
                if !done.status.success() {
                    // M4-D16: the run fails (kind other) with the child's
                    // error text as the message; with none, a line of our
                    // own naming the exit status.
                    let err = String::from_utf8_lossy(&done.stderr);
                    let msg = match err.trim_end_matches(['\n', '\r']) {
                        "" => format!(
                            "Error: {} exited with {}.",
                            name,
                            done.status.code().unwrap_or(1)
                        ),
                        text => text.to_string(),
                    };
                    return Err(TErr::Fatal(msg));
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::Exit { code } => {
                // M4-S77: the drops of the current run unwind first (the
                // active scopes' cleanups, innermost first); the other
                // tasks end with the run in the eager cut (logged); then
                // the process exits with the code.
                while let Some(scope) = frame.pop() {
                    let _ = self.run_cleanups(scope, out);
                }
                Err(TErr::Exit(*code))
            }
            sem::Stmt::WhenSignal { signal, body } => {
                // M4-S79: the block registers for the signal; the poll at
                // every sentence boundary runs it when the flag arrives.
                self.signal_handlers.push((*signal, body.clone()));
                Ok(Flow::Normal)
            }
            sem::Stmt::ForEachInput { var, body } => {
                // M4-G27/S85: the lines of standard input, buffered first
                // (the runners read stdin once - logged), each without its
                // line ending, streamed from the buffer. Stop. leaves the
                // loop; the var is the line and so is it.
                let text = self.input.clone();
                // empty standard input holds no lines at all (a split of
                // an empty text would give one empty round)
                let mut lines: Vec<String> = if text.is_empty() {
                    Vec::new()
                } else {
                    text.split('\n')
                        .map(|l| l.trim_end_matches('\r').to_string())
                        .collect()
                };
                if text.ends_with('\n') {
                    lines.pop(); // the empty piece after the last line feed
                }
                for line in lines {
                    self.tick()?;
                    frame.last_result = Some(Value::Text(line.clone()));
                    frame.push();
                    frame.define(var.as_str(), Value::Text(line.clone()));
                    let flow = self.exec_stmts(body, frame, out);
                    let _ = self.run_cleanups(frame.pop().unwrap_or_default(), out);
                    match flow {
                        Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                        Ok(Flow::Stop) => break,
                        Ok(Flow::Hand(v)) => {
                            if self.in_generator {
                                self.pending_hands.push(v);
                            } else {
                                return Ok(Flow::Hand(v));
                            }
                        }
                        Ok(f @ Flow::Back(_, _)) => return Ok(f),
                        Err(e) => return Err(e),
                    }
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::HandBack(e) => {
                let v = self.eval_expr(e, frame, out)?;
                Ok(Flow::Hand(v))
            }
            sem::Stmt::DefineLocalFn(f) => {
                // A local function is a closure (M3-D2): it sees every name
                // visible at its definition. The snapshot carries those names.
                let mut captures: Vec<(String, Value)> = Vec::new();
                for sc in frame.scopes.iter() {
                    for (n, v) in sc.vars.iter() {
                        if f.inputs.iter().any(|(i, _)| i == n) {
                            continue;
                        }
                        captures.push((n.clone(), v.clone()));
                    }
                }
                captures.reverse();
                captures.dedup_by(|a, b| a.0 == b.0);
                frame.define(
                    &f.name,
                    Value::Closure {
                        func: f.name.clone(),
                        captures,
                    },
                );
                Ok(Flow::Normal)
            }
            sem::Stmt::Define(d) => {
                let v = self.eval_with_fallback(&d.expr, &d.fallback, frame, out)?;
                frame.define(&d.name, v);
                Ok(Flow::Normal)
            }
            sem::Stmt::Set { name, expr } => {
                let v = self.eval_expr(expr, frame, out)?;
                // M4-D3: a guarded name is fixed but changes through Set;
                // the guard itself stays, the inner value is replaced (each
                // sentence takes the lock - unobservable in the eager cut).
                // An atomic or counter refuses Set (only Add changes it);
                // the compiler rejects Set on them, this is the runtime belt.
                if let Some(slot) = frame.find_mut(name) {
                    match slot {
                        Value::Guarded(inner) => {
                            **inner = v;
                            return Ok(Flow::Normal);
                        }
                        Value::Atomic(_) | Value::Counter(_) => {
                            return Err(fatal(
                                "T0406",
                                "Only a guarded value changes with Set; an atomic changes with Add atomically and a counter with Add.",
                                "Use Add on it, or guard it if Set must change it.",
                            ));
                        }
                        _ => {}
                    }
                }
                frame.assign(name, v);
                Ok(Flow::Normal)
            }
            sem::Stmt::Ask {
                name,
                kind,
                fallback,
            } => {
                self.tick()?;
                // M4-S86: when no person is at the other end (standard
                // input is not a terminal), Ask fails with kind other, the
                // message "no person here" - even when standard input has
                // piped text (Read input is the sentence for that).
                if !self.interactive {
                    return Err(TErr::Fatal("Error: no person here.".to_string()));
                }
                let reply = self.read_line();
                let v = match kind {
                    sem::AskKind::Text => Value::Text(reply),
                    sem::AskKind::Number | sem::AskKind::Decimal => match parse_number(&reply) {
                        Some(n) => {
                            if matches!(kind, sem::AskKind::Decimal) {
                                match n {
                                    Value::Whole(w) => Value::Dec(w as f64),
                                    d @ Value::Dec(_) => d,
                                    other => other,
                                }
                            } else {
                                n
                            }
                        }
                        None => match fallback {
                            Some(fb) => self.eval_expr(fb, frame, out)?,
                            None => {
                                return Err(TErr::Fatal(
                                    "Error: The reply is not a number.".to_string(),
                                ));
                            }
                        },
                    },
                };
                frame.assign(name, v);
                Ok(Flow::Normal)
            }
            sem::Stmt::Say { expr, mods, lines } => {
                if !lines.is_empty() && matches!(&expr.e, E::Flat(v) if v.is_empty()) {
                    // M3c-4: the join of per-line-trimmed texts is exactly
                    // what last_shown keeps and out receives - the buffer
                    // never escapes with a different value, so it comes
                    // from the transient pool.
                    let mut scratch = self.pool.lease_text();
                    for line in lines {
                        if !scratch.is_empty() {
                            scratch.push(' ');
                        }
                        scratch.push_str(line.trim());
                    }
                    frame.last_shown = scratch.trim().to_string();
                    for line in lines {
                        out.push_str(line.trim());
                        if !mods.without_newline {
                            out.push('\n');
                        }
                    }
                    self.pool.keep_text(scratch);
                    return Ok(Flow::Normal);
                }
                if let E::Flat(pieces) = &expr.e {
                    // A run of words: widths and places apply to the run.
                    // M3c-4: the parts vec and the join buffer are pooled;
                    // both are drained/read before the giveaway.
                    let mut parts = self.pool.lease_parts();
                    for p in pieces {
                        let v = self.eval_expr(p, frame, out)?;
                        parts.push(self.show_value(&v, mods));
                    }
                    let mut text = self.pool.lease_text();
                    for (pi, s) in parts.iter().enumerate() {
                        if pi > 0 {
                            text.push(' ');
                        }
                        text.push_str(s);
                    }
                    if let Some(w) = mods.width {
                        if text.chars().count() < w {
                            text = format!("{}{}", " ".repeat(w - text.chars().count()), text);
                        }
                    }
                    frame.last_shown = text.trim().to_string();
                    out.push_str(&text);
                    if !mods.without_newline {
                        out.push('\n');
                    }
                    self.pool.keep_text(text);
                    self.pool.keep_parts(parts);
                    return Ok(Flow::Normal);
                }
                let v = self.eval_expr(expr, frame, out)?;
                let text = self.show_value(&v, mods);
                frame.last_shown = text.trim().to_string();
                out.push_str(&text);
                if !mods.without_newline {
                    out.push('\n');
                }
                self.pool.keep_text(text);
                Ok(Flow::Normal)
            }
            sem::Stmt::Log {
                level,
                expr,
                mods,
                lines,
            } => {
                // M4-S87: the line is written only when the run's level
                // admits it (S88); the text is built exactly as a Say
                // builds it (names replaced, a secret as hidden).
                if level.rank() >= self.log_level.rank() {
                    let text = self.log_text(expr, mods, lines, frame, out)?;
                    // M4-D11/D12: to standard error, as LEVEL TEXT and a
                    // line feed, in the one merged stream in order; the
                    // byte range lets the real front ends split it.
                    let start = out.len();
                    if text.is_empty() {
                        out.push_str(level.word());
                    } else {
                        out.push_str(level.word());
                        out.push(' ');
                        out.push_str(&text);
                    }
                    out.push('\n');
                    self.err_ranges.push((start, out.len()));
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::LogLevel { level } => {
                // M4-S88: Use log level LEVEL. sets the run's level.
                self.log_level = *level;
                Ok(Flow::Normal)
            }
            // ---- M4-10 (Appendix K 7.8 network) ----
            sem::Stmt::Fetch {
                method,
                address,
                data,
                headers,
                query,
                skip_tls,
            } => self.exec_fetch(
                *method,
                address,
                data.as_ref(),
                headers,
                query,
                *skip_tls,
                frame,
                out,
            ),
            sem::Stmt::PostTo { data, address } => {
                // M4-S60: Post x to address is Fetch address using post
                // with data x.
                self.exec_fetch(
                    sem::NetMethod::Post,
                    address,
                    Some(data),
                    &[],
                    &[],
                    false,
                    frame,
                    out,
                )
            }
            sem::Stmt::Serve {
                port,
                secure,
                cert,
                key,
                body,
            } => self.exec_serve(*port, *secure, cert, key, body, frame, out),
            // handlers, live blocks and page declarations are consumed
            // by Serve's execution; a stray one is inert (the compiler
            // refuses them outside a Serve block anyway)
            sem::Stmt::WhenSomeone { .. }
            | sem::Stmt::WhenLive { .. }
            | sem::Stmt::PageDecl { .. } => Ok(Flow::Normal),
            sem::Stmt::Careful { body } => {
                // S62: Be careful. runs its body inline (it guards the
                // dangerous sentences, it does not change execution)
                self.exec_stmts(body, frame, out)?;
                Ok(Flow::Normal)
            }
            sem::Stmt::Respond { kind } => {
                // M4-S69: the answer. The first Respond on the path
                // answers; the compile checks are T0166 (no Respond) and
                // T0168 (two Responds).
                let resp = self.build_response(kind, frame, out)?;
                let Some(ctx) = self.handler_ctx.as_mut() else {
                    return Err(fatal(
                        "T0113",
                        "Respond runs outside a handler.",
                        "Respond belongs in a When someone block.",
                    ));
                };
                ctx.response = Some(resp);
                // the body ends here (the response rides out with it)
                Ok(Flow::Stop)
            }
            sem::Stmt::WsSend { value } => {
                // M4-S73: Send x to connection. sends one text frame (the
                // shown wording of x).
                let v = self.eval_expr(value, frame, out)?;
                let text = self.show_value(&v, &SayMods::default());
                if let Some(id) = self.active_conn {
                    // the parked-session model (M4-D13 route A): the
                    // frame goes to this session's connection
                    self.live_send(id, &text)?;
                    return Ok(Flow::Normal);
                }
                let Some(ctx) = &self.handler_ctx else {
                    return Err(fatal(
                        "T0113",
                        "Send to connection runs outside a live block.",
                        "Send to connection belongs in a When someone opens live block.",
                    ));
                };
                let Some(ws) = &ctx.ws else {
                    return Err(TErr::Signal);
                };
                let frame_data = net::ws_server_frame(text.as_bytes());
                let mut w = ws.borrow_mut();
                w.conn.write(&frame_data).map_err(|_| TErr::Signal)?;
                w.conn.flush().map_err(|_| TErr::Signal)?;
                Ok(Flow::Normal)
            }
            sem::Stmt::WsRecv => {
                // M4-S73: Receive from connection. gives maybe text;
                // missing when the other side closed. The value is it.
                if let Some(id) = self.active_conn {
                    // the parked-session model: one non-blocking read;
                    // no frame yet parks the session at this statement
                    // (the pc sits back on it and it re-runs on resume)
                    match self.live_recv(id)? {
                        Some(v) => frame.last_result = Some(v),
                        None => {}
                    }
                    return Ok(Flow::Normal);
                }
                let Some(ctx) = &self.handler_ctx else {
                    return Err(fatal(
                        "T0113",
                        "Receive from connection runs outside a live block.",
                        "Receive from connection belongs in a When someone opens live block.",
                    ));
                };
                let Some(ws) = &ctx.ws else {
                    return Err(TErr::Signal);
                };
                let v = {
                    let mut w = ws.borrow_mut();
                    let result = net::ws_read_frame(&mut |buf| w.conn.read(buf));
                    match result {
                        Ok(Some((1, payload))) => match String::from_utf8(payload) {
                            Ok(t) => Ok(Value::Text(t)),
                            Err(_) => Err(TErr::Signal),
                        },
                        Ok(Some(_)) => Ok(Value::Missing),
                        Ok(None) => Ok(Value::Missing), // the other side closed
                        Err(e) if e.message.contains("closed") => Ok(Value::Missing),
                        Err(_) => Err(TErr::Signal),
                    }
                };
                frame.last_result = Some(v?);
                Ok(Flow::Normal)
            }
            sem::Stmt::ForIn { vars, list, body } => {
                let v = self.eval_expr(list, frame, out)?;
                match v {
                    Value::Map(entries) => {
                        for (k, val) in entries {
                            self.tick()?;
                            frame.push();
                            frame.define(&vars[0], k.clone());
                            if vars.len() > 1 {
                                frame.define(&vars[1], val.clone());
                            }
                            let flow = self.exec_stmts(body, frame, out);
                            frame.pop();
                            match flow {
                                Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                                Ok(Flow::Stop) => return Ok(Flow::Normal),
                                Ok(Flow::Hand(v)) => {
                                    if self.in_generator {
                                        self.pending_hands.push(v);
                                    } else {
                                        return Ok(Flow::Hand(v));
                                    }
                                }
                                Ok(f @ Flow::Back(_, _)) => return Ok(f),
                                Err(e) => return Err(e),
                            }
                        }
                    }
                    rest => match rest {
                        Value::List(items) => {
                            for item in items {
                                self.tick()?;
                                frame.push();
                                frame.define(&vars[0], item);
                                let flow = self.exec_stmts(body, frame, out);
                                frame.pop();
                                match flow {
                                    Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                                    Ok(Flow::Stop) => return Ok(Flow::Normal),
                                    Ok(Flow::Hand(v)) => {
                                        if self.in_generator {
                                            self.pending_hands.push(v);
                                        } else {
                                            return Ok(Flow::Hand(v));
                                        }
                                    }
                                    Ok(f @ Flow::Back(_, _)) => return Ok(f),
                                    Err(e) => return Err(e),
                                }
                            }
                        }
                        other => {
                            // M3c-4: a non-list payload iterates through a
                            // one-slot pooled vec; elements move out exactly
                            // as before (drain keeps the buffer alive) and
                            // the buffer is given back after the loop.
                            let mut one = self.pool.lease_single();
                            one.push(other);
                            for item in one.drain(..) {
                                self.tick()?;
                                frame.push();
                                frame.define(&vars[0], item);
                                let flow = self.exec_stmts(body, frame, out);
                                frame.pop();
                                match flow {
                                    Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                                    Ok(Flow::Stop) => return Ok(Flow::Normal),
                                    Ok(Flow::Hand(v)) => {
                                        if self.in_generator {
                                            self.pending_hands.push(v);
                                        } else {
                                            return Ok(Flow::Hand(v));
                                        }
                                    }
                                    Ok(f @ Flow::Back(_, _)) => return Ok(f),
                                    Err(e) => return Err(e),
                                }
                            }
                            self.pool.keep_single(one);
                        }
                    },
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::Evaluate { expr, .. } => {
                let v = self.eval_expr(expr, frame, out)?;
                frame.last_result = Some(v);
                Ok(Flow::Normal)
            }
            sem::Stmt::Append { value, list } => {
                // M4-S20: a counter is an atomic whole number; "Add V to
                // hits." on a counter adds (parse turns this into AtomicAdd
                // when the kind is known; this arm is the runtime fall-through).
                if matches!(frame.find(list), Some(Value::Counter(_))) {
                    let v = unwrap_shared_read(self.eval_expr(value, frame, out)?);
                    let Value::Whole(m) = v else {
                        return Err(fatal(
                            "T0113",
                            "The value added to a counter is not a whole number.",
                            "Add a whole number.",
                        ));
                    };
                    if let Some(Value::Counter(n)) = frame.find_mut(list) {
                        *n = n.wrapping_add(m);
                    }
                    return Ok(Flow::Normal);
                }
                let v = self.eval_expr(value, frame, out)?;
                let cur = frame.find(list).cloned();
                match cur {
                    Some(Value::List(mut items)) => {
                        items.push(v);
                        frame.assign(list, Value::List(items));
                        Ok(Flow::Normal)
                    }
                    Some(_) => Err(fatal(
                        "T0305",
                        &format!("Add works on lists, and {list} is not one."),
                        "Use a kind the word accepts.",
                    )),
                    None => Err(fatal(
                        "T0205",
                        &format!("{list} is not defined."),
                        "Name it first.",
                    )),
                }
            }
            sem::Stmt::Put { map, key, value } => {
                let v = self.eval_expr(value, frame, out)?;
                let cur = frame.find(map).cloned();
                match cur {
                    Some(Value::Map(mut entries)) => {
                        let Some(k) = key else {
                            return Err(fatal(
                                "T0305",
                                &format!("Put into a map needs a key under {map}."),
                                "Write under <key>.",
                            ));
                        };
                        let k = self.eval_expr(&k, frame, out)?;
                        if let Some(pos) = entries.iter().position(|(ek, _)| cmp_eq(ek, &k)) {
                            entries[pos].1 = v;
                        } else {
                            entries.push((k, v));
                        }
                        frame.assign(map, Value::Map(entries));
                        Ok(Flow::Normal)
                    }
                    Some(Value::Set(mut items)) => {
                        if key.is_some() {
                            return Err(fatal(
                                "T0305",
                                &format!("Put into a set takes no key: Put v in {map}."),
                                "Remove the under <key> part.",
                            ));
                        }
                        if !items.iter().any(|it| cmp_eq(it, &v)) {
                            items.push(v);
                        }
                        frame.assign(map, Value::Set(items));
                        Ok(Flow::Normal)
                    }
                    Some(_) => Err(fatal(
                        "T0305",
                        &format!("Put works on maps and sets, and {map} is not one."),
                        "Use a map or set.",
                    )),
                    None => Err(fatal(
                        "T0205",
                        &format!("{map} is not defined."),
                        "Name it first.",
                    )),
                }
            }
            sem::Stmt::Remove { coll, value } => {
                let v = self.eval_expr(value, frame, out)?;
                let cur = frame.find(coll).cloned();
                match cur {
                    Some(Value::List(mut items)) => {
                        if let Some(pos) = items.iter().position(|it| cmp_eq(it, &v)) {
                            items.remove(pos);
                        }
                        frame.assign(coll, Value::List(items));
                        Ok(Flow::Normal)
                    }
                    Some(Value::Set(mut items)) => {
                        items.retain(|it| !cmp_eq(it, &v));
                        frame.assign(coll, Value::Set(items));
                        Ok(Flow::Normal)
                    }
                    Some(Value::Map(mut entries)) => {
                        entries.retain(|(ek, _)| !cmp_eq(ek, &v));
                        frame.assign(coll, Value::Map(entries));
                        Ok(Flow::Normal)
                    }
                    Some(_) => Err(fatal(
                        "T0305",
                        &format!("Remove works on lists, sets and maps, and {coll} is not one."),
                        "Use a collection.",
                    )),
                    None => Err(fatal(
                        "T0205",
                        &format!("{coll} is not defined."),
                        "Name it first.",
                    )),
                }
            }
            sem::Stmt::RemoveFirst { coll } => {
                let cur = frame.find(coll).cloned();
                match cur {
                    Some(Value::Queue(mut items)) => {
                        if items.is_empty() {
                            Err(fatal(
                                "T0613",
                                &format!("Remove first from an empty {coll}."),
                                "Test with is empty first.",
                            ))
                        } else {
                            items.remove(0);
                            frame.assign(coll, Value::Queue(items));
                            Ok(Flow::Normal)
                        }
                    }
                    Some(Value::List(mut items)) => {
                        if items.is_empty() {
                            Err(fatal(
                                "T0613",
                                &format!("Remove first from an empty {coll}."),
                                "Test with is empty first.",
                            ))
                        } else {
                            items.remove(0);
                            frame.assign(coll, Value::List(items));
                            Ok(Flow::Normal)
                        }
                    }
                    Some(_) => Err(fatal(
                        "T0305",
                        &format!("Remove first works on queues and lists, and {coll} is not one."),
                        "Use a queue or list.",
                    )),
                    None => Err(fatal(
                        "T0205",
                        &format!("{coll} is not defined."),
                        "Name it first.",
                    )),
                }
            }
            sem::Stmt::Stop => Ok(Flow::Stop),
            sem::Stmt::Skip => Ok(Flow::Skip),
            sem::Stmt::GiveBack(v) => {
                let value = match v {
                    Some(e) => self.eval_expr(e, frame, out)?,
                    None => Value::Missing,
                };
                Ok(Flow::Back(value, false))
            }
            sem::Stmt::If { branches, other } => self.exec_if(branches, other, frame, out),
            sem::Stmt::SetPart { path, expr } => {
                // Set age of maya to 32. (ch.20)
                let v = self.eval_expr(expr, frame, out)?;
                let (base, parts) = match path.split_last() {
                    Some(x) => x,
                    None => {
                        return Err(fatal(
                            "T0606",
                            "A Set with no part path.",
                            "Write the part and the record.",
                        ));
                    }
                };
                let cur = match frame.find_mut(base) {
                    Some(x) => x,
                    None => {
                        return Err(fatal(
                            "T0205",
                            &format!("{base} is not defined."),
                            "Name it first.",
                        ));
                    }
                };
                // the path runs part of part of ... base (outermost last):
                // walk it from the base inward
                let inward: Vec<String> = parts.iter().rev().cloned().collect();
                // the Always invariants of the (outermost) record re-run when
                // the program changes a part through any depth of the path
                // (ch.64, M3-S38) ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬Ãƒâ€¦Ã‚Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â checked AFTER the write, over the new
                // part values
                set_part_into(cur, &inward, &v)?;
                let inv_target = frame.find(base).and_then(|c| match c {
                    Value::Record(t, r) => Some((t.clone(), r.clone())),
                    _ => None,
                });
                match inv_target {
                    Some((tn, r)) => {
                        let site = (
                            std::ptr::from_ref(expr) as usize,
                            if parts.len() == 1 {
                                vec![(parts[0].clone(), expr.clone())]
                            } else {
                                Vec::new()
                            },
                        );
                        self.run_always(&tn, &r, Some((site.0, &site.1)), out)?
                    }
                    None => {}
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::DefineEnum { name, variants } => {
                // every shape name becomes a value; shapes with parts are made
                // with their parts at the construction site (ch.21)
                let _ = (name, variants.len());
                for (shape, _) in variants {
                    frame.define(
                        shape,
                        Value::Enum {
                            variant: shape.clone(),
                            parts: Vec::new(),
                        },
                    );
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::LookAt { value, whens } => {
                // Look at takes an enum apart; the When for the met shape runs
                // with fresh names for its parts (ch.21)
                let v = self.eval_expr(value, frame, out)?;
                let (variant, parts): (String, Vec<Value>) = match &v {
                    Value::Enum { variant, parts } => (variant.clone(), parts.clone()),
                    _ => {
                        return Err(fatal(
                            "T0606",
                            "A Look at ran on a value that holds no shape.",
                            "Look at a value from an enum.",
                        ));
                    }
                };
                for w in whens {
                    if w.shape == variant {
                        frame.push();
                        for (n, val) in w.names.iter().zip(parts.iter()) {
                            frame.define(n, val.clone());
                        }
                        let flow = self.exec_stmts(&w.body, frame, out);
                        frame.pop();
                        return flow;
                    }
                }
                Err(fatal(
                    "T0606",
                    "The program met a shape no When block handles.",
                    "Add a When block for every shape.",
                ))
            }
            sem::Stmt::Try {
                sentence,
                success,
                failure,
            } => {
                // Try runs one sentence that can fail; on failure the matching
                // If that fails block runs (ch.19).
                let failed = match self.exec_stmt(&sentence, frame, out) {
                    Err(TErr::Signal) => true,
                    Ok(Flow::Back(_, true)) => true,
                    Ok(Flow::Back(v, false)) => {
                        frame.last_result = Some(v);
                        false
                    }
                    Ok(Flow::Normal) => false,
                    Ok(f) => return Ok(f),
                    Err(e) => return Err(e),
                };
                if failed {
                    // Fail with makes a failure of kind "other" (ch.19).
                    let kind = "other".to_string();
                    let handled = failure.iter().find(|(k, _)| match k {
                        Some(kk) => kk == &kind,
                        None => true,
                    });
                    if let Some((_, body)) = handled {
                        frame.push();
                        let flow = self.exec_stmts(body, frame, out);
                        frame.pop();
                        return flow;
                    }
                    // no block names this failure: pass it up
                    return Ok(Flow::Back(Value::Text(String::new()), true));
                }
                self.exec_stmts(success, frame, out)
            }
            sem::Stmt::Fail { message } => {
                // Fail with TEXT: a failure of kind other (ch.19).
                let v = self.eval_expr(message, frame, out)?;
                Ok(Flow::Back(v, true))
            }
            sem::Stmt::PassFailureUp => {
                // Pass failure up. returns the current failure to the caller
                // (ch.19); only legal inside a can fail function, checked when
                // the tree is built.
                Ok(Flow::Back(Value::Text(String::new()), true))
            }
            sem::Stmt::Close { name } => {
                // Close x. finishes x early (ch.31). A closed channel keeps
                // its queue but refuses further sends (M4-S14, T0609); other
                // kinds have no run-time close state in this cut (deviation
                // logged: files close on drop).
                if let Some(Value::Channel(state)) = frame.find(name) {
                    state.borrow_mut().closed = true;
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::Share { .. } | sem::Stmt::Use { .. } | sem::Stmt::Test { .. } => {
                // compile-time concerns; tests are removed from release builds
                Ok(Flow::Normal)
            }
            sem::Stmt::Pretend { name, value } => {
                // Pretend f gives V. replaces a function for this test (ch.38)
                let v = self.eval_expr(value, frame, out)?;
                self.pretend.insert(name.clone(), v);
                Ok(Flow::Normal)
            }
            sem::Stmt::Check {
                text,
                cond,
                must_fail,
                prop,
                body,
            } => {
                if let Some((kind_words, gen_name)) = prop {
                    // Check for any <kind> <name>. ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Â ÃƒÂ¢Ã¢â€šÂ¬Ã¢â€žÂ¢ÃƒÆ’Ã†â€™ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã¢â‚¬Â¦Ãƒâ€šÃ‚Â¡ÃƒÆ’Ã†â€™ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬Ãƒâ€¦Ã‚Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã†â€™ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â property test (ch.38):
                    // 100 inputs, seed 42. No shrinking (deviation).
                    let mut state: u64 = 42;
                    let mut next = || {
                        state = state
                            .wrapping_mul(6364136223846793005)
                            .wrapping_add(1442695040888963407);
                        (state >> 33) as u64
                    };
                    let before = self.failed_checks.len();
                    for _ in 0..100 {
                        let v = gen_value(kind_words, &mut next);
                        frame.push();
                        frame.define(&gen_name.clone(), v.clone());
                        let r = self.exec_stmts(body, frame, out);
                        frame.pop();
                        if r.is_err() || self.failed_checks.len() > before {
                            let inner = self.failed_checks.get(before).cloned().unwrap_or_default();
                            let why = match (&r, inner.is_empty()) {
                                (Err(TErr::Fatal(m)), _) => format!(" ({m})"),
                                (Err(TErr::Signal), _) => {
                                    " (a can fail sentence failed.)".to_string()
                                }
                                (_, false) => format!(" ({inner})"),
                                (_, true) => String::new(),
                            };
                            self.failed_checks.truncate(before);
                            self.failed_checks.push(format!(
                                "{text} failed for {gen_name} = {}.{}",
                                self.show_value(&v, &SayMods::default()),
                                why
                            ));
                            return Ok(Flow::Normal);
                        }
                    }
                    return Ok(Flow::Normal);
                }
                if let Some(c) = cond {
                    let v = self.eval_expr(c, frame, out)?;
                    if !matches!(v, Value::Boolean(true)) {
                        let detail = match &c.e {
                            E::Compare(comp) => {
                                let lv = self
                                    .eval_expr(&comp.l, frame, out)
                                    .unwrap_or(Value::Missing);
                                let rv = match comp.r.first() {
                                    Some(r) => {
                                        self.eval_expr(r, frame, out).unwrap_or(Value::Missing)
                                    }
                                    None => Value::Missing,
                                };
                                let dummy = SayMods::default();
                                format!(
                                    " (they were {} and {})",
                                    self.show_value(&lv, &dummy),
                                    self.show_value(&rv, &dummy)
                                )
                            }
                            _ => String::new(),
                        };
                        let label = if text.is_empty() {
                            format!("Check that {} failed.", c.dis.trim_end_matches('.'))
                        } else {
                            format!("{text} failed.")
                        };
                        self.failed_checks.push(format!("{label}{detail}"));
                    }
                    return Ok(Flow::Normal);
                }
                // Check that this fails. passes when a sentence inside fails.
                self.in_must_fail += 1;
                let r = self.exec_stmts(body, frame, out);
                self.in_must_fail -= 1;
                if matches!(r, Ok(_)) {
                    self.failed_checks
                        .push("Check that this fails. failed. (nothing inside failed)".to_string());
                }
                Ok(Flow::Normal)
            }
            sem::Stmt::RepeatTimes { count, body } => {
                let limit = self.eval_expr(count, frame, out)?;
                let limit = as_i64(&limit);
                frame.counters.push((1, limit));
                let mut ok = Ok(Flow::Normal);
                loop {
                    self.tick()?;
                    let Some(&(cur, lim)) = frame.counters.last() else {
                        break;
                    };
                    if cur > lim {
                        break;
                    }
                    frame.push();
                    let flow = self.exec_stmts(body, frame, out);
                    frame.pop();
                    match flow {
                        Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                        Ok(Flow::Stop) => break,
                        Ok(Flow::Hand(v)) => {
                            if self.in_generator {
                                self.pending_hands.push(v);
                            } else {
                                ok = Ok(Flow::Hand(v));
                                break;
                            }
                        }
                        Ok(f @ Flow::Back(_, _)) => {
                            ok = Ok(f);
                            break;
                        }
                        Err(e) => {
                            ok = Err(e);
                            break;
                        }
                    }
                    if let Some(last) = frame.counters.last_mut() {
                        last.0 = last.0.saturating_add(1);
                    }
                }
                frame.counters.pop();
                ok
            }
            sem::Stmt::RepeatForever { body } => loop {
                self.tick()?;
                frame.push();
                let flow = self.exec_stmts(body, frame, out);
                frame.pop();
                match flow {
                    Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                    Ok(Flow::Stop) => return Ok(Flow::Normal),
                    Ok(Flow::Hand(v)) => {
                        if self.in_generator {
                            self.pending_hands.push(v);
                        } else {
                            return Ok(Flow::Hand(v));
                        }
                    }
                    Ok(f @ Flow::Back(_, _)) => return Ok(f),
                    Err(e) => return Err(e),
                }
            },
            sem::Stmt::RepeatWhile { cond, body } => loop {
                self.tick()?;
                let c = self.eval_expr(cond, frame, out)?;
                if !as_truthy(&c) {
                    break Ok(Flow::Normal);
                }
                frame.push();
                let flow = self.exec_stmts(body, frame, out);
                frame.pop();
                match flow {
                    Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                    Ok(Flow::Stop) => return Ok(Flow::Normal),
                    Ok(Flow::Hand(v)) => {
                        if self.in_generator {
                            self.pending_hands.push(v);
                        } else {
                            return Ok(Flow::Hand(v));
                        }
                    }
                    Ok(f @ Flow::Back(_, _)) => return Ok(f),
                    Err(e) => return Err(e),
                }
            },
            sem::Stmt::ForRange {
                var,
                from,
                to,
                body,
            } => {
                let start = self.eval_expr(from, frame, out)?;
                let end = as_i64(&self.eval_expr(to, frame, out)?);
                let mut n = as_i64(&start);
                loop {
                    self.tick()?;
                    if n > end {
                        break;
                    }
                    frame.push();
                    frame.define(var, Value::Whole(n));
                    let flow = self.exec_stmts(body, frame, out);
                    frame.pop();
                    match flow {
                        Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                        Ok(Flow::Stop) => return Ok(Flow::Normal),
                        Ok(Flow::Hand(v)) => {
                            if self.in_generator {
                                self.pending_hands.push(v);
                            } else {
                                return Ok(Flow::Hand(v));
                            }
                        }
                        Ok(f @ Flow::Back(_, _)) => return Ok(f),
                        Err(e) => return Err(e),
                    }
                    n = n.saturating_add(1);
                }
                Ok(Flow::Normal)
            }
        }
    }

    fn exec_if(
        &mut self,
        branches: &[(sem::Expr, Vec<sem::Stmt>)],
        other: &Option<Vec<sem::Stmt>>,
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Flow> {
        for (cond, body) in branches {
            self.tick()?;
            let truth = self.eval_expr(cond, frame, out)?;
            if as_truthy(&truth) {
                frame.push();
                let flow = self.exec_stmts(body, frame, out);
                frame.pop();
                return flow;
            }
        }
        if let Some(ob) = other {
            frame.push();
            let flow = self.exec_stmts(ob, frame, out);
            frame.pop();
            return flow;
        }
        Ok(Flow::Normal)
    }

    // ------------------------------------------------------------ expressions

    /// A can-fail value with its "If that fails" value.
    fn eval_with_fallback(
        &mut self,
        expr: &sem::Expr,
        fallback: &Option<sem::Expr>,
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Value> {
        match self.eval_expr(expr, frame, out) {
            Ok(v) => Ok(v),
            Err(TErr::Signal) => match fallback {
                Some(fb) => match self.eval_expr(fb, frame, out) {
                    Ok(v) => Ok(v),
                    Err(TErr::Signal) | Err(TErr::Fatal(_)) | Err(TErr::Yield(_)) => Err(
                        TErr::Fatal("Error: That text cannot be read as a number.".to_string()),
                    ),
                    // M4-8: an Exit inside the fallback still ends the run
                    Err(e @ TErr::Exit(_)) => Err(e),
                },
                None => Err(TErr::Fatal(
                    "Error: That text cannot be read as a number.".to_string(),
                )),
            },
            Err(e) => Err(e),
        }
    }

    /// M4-7 (S54): one 64-bit draw from the program's generator. The
    /// state is created on first use: a run without Use seed seeds it
    /// from the operating system's entropy, a test run starts at 42.
    fn rng_next(&mut self) -> u64 {
        if self.rng.is_none() {
            self.rng = Some(crate::time4::xoshiro_seed(crate::time4::os_seed()));
        }
        crate::time4::xoshiro_next(self.rng.as_mut().unwrap())
    }

    fn eval_expr(&mut self, e: &sem::Expr, frame: &mut Frame, out: &mut String) -> R<Value> {
        match &e.e {
            E::Whole(v) => Ok(Value::Whole(*v)),
            E::Dec(v) => Ok(Value::Dec(*v)),
            E::Boolean(v) => Ok(Value::Boolean(*v)),
            E::Missing => Ok(Value::Missing),
            E::Word(t) => Ok(Value::Text(t.clone())),
            E::Name(n) => Ok(unwrap_shared_read(
                frame.find(n).cloned().unwrap_or(Value::Missing),
            )),
            E::It => {
                if let Some(item) = &frame.where_item {
                    return Ok(item.clone());
                }
                match &frame.last_result {
                    Some(Value::List(_)) => Err(fatal(
                        "T0221",
                        "it is used for a list. Use them.",
                        "Use them.",
                    )),
                    Some(v) => Ok(v.clone()),
                    None => Err(fatal(
                        "T0220",
                        &it_too_far(&frame.last_shown),
                        "Name the result.",
                    )),
                }
            }
            E::Them => match &frame.last_result {
                Some(Value::List(items)) => Ok(Value::List(items.clone())),
                Some(_) => Err(fatal(
                    "T0222",
                    "them means the list from the sentence just before. Use it for one value.",
                    "Use them.",
                )),
                None => Err(fatal(
                    "T0220",
                    &it_too_far(&frame.last_shown),
                    "Name the result.",
                )),
            },
            E::Sorted(inner, ascending) => match self.eval_expr(inner, frame, out)? {
                Value::List(mut items) => {
                    items.sort_by(|a, b| {
                        let (Some(x), Some(y)) = (numeric(a), numeric(b)) else {
                            return as_text(a).cmp(&as_text(b));
                        };
                        let ord = x.partial_cmp(&y).unwrap_or(std::cmp::Ordering::Equal);
                        if *ascending { ord } else { ord.reverse() }
                    });
                    Ok(Value::List(items))
                }
                other => Ok(other),
            },
            E::Reverse(inner) => match self.eval_expr(inner, frame, out)? {
                Value::List(mut items) => {
                    items.reverse();
                    Ok(Value::List(items))
                }
                Value::Text(t) => Ok(Value::Text(graphemes_of(&t).rev().collect())),
                other => Ok(other),
            },
            E::Upper(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                Ok(Value::Text(as_text(&v).to_uppercase()))
            }
            E::Trimmed(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                Ok(Value::Text(as_text(&v).trim().to_string()))
            }
            E::Normalized(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                use unicode_normalization::UnicodeNormalization;
                Ok(Value::Text(as_text(&v).nfc().collect()))
            }
            E::PatWords { .. } => {
                // a pattern is only used inside replace, position of or split
                Ok(Value::Text(String::new()))
            }
            E::Unique(inner) => match self.eval_expr(inner, frame, out)? {
                Value::List(items) => {
                    let mut kept: Vec<Value> = Vec::new();
                    for it in items {
                        if !kept.contains(&it) {
                            kept.push(it);
                        }
                    }
                    Ok(Value::List(kept))
                }
                other => Ok(other),
            },
            E::Fallback { value, default } => {
                let v = self.eval_expr(value, frame, out)?;
                match v {
                    Value::Maybe(m) => match m {
                        Some(x) => Ok(*x),
                        None => self.eval_expr(default, frame, out),
                    },
                    Value::Missing => self.eval_expr(default, frame, out),
                    other => Ok(other),
                }
            }

            E::Combine { list, word } => {
                let v = self.eval_expr(list, frame, out)?;
                match v {
                    Value::List(items) if !items.is_empty() => {
                        let mut acc = items[0].clone();
                        for it in &items[1..] {
                            acc = combine_step(acc, it.clone(), word)?;
                        }
                        Ok(acc)
                    }
                    Value::List(_) => Ok(Value::Whole(0)),
                    other => Ok(other),
                }
            }
            E::ApplyEach { name, list } => {
                let v = self.eval_expr(list, frame, out)?;
                match v {
                    Value::List(items) => {
                        let mut mapped = Vec::new();
                        for it in items {
                            mapped.push(self.eval_call_values(name, &[it], frame, out)?);
                        }
                        Ok(Value::List(mapped))
                    }
                    other => Ok(other),
                }
            }
            E::ListOf(items) => {
                let mut vals = Vec::new();
                for it in items {
                    vals.push(self.eval_expr(it, frame, out)?);
                }
                Ok(Value::List(vals))
            }
            E::PairOf(a, b) => {
                let x = self.eval_expr(a, frame, out)?;
                let y = self.eval_expr(b, frame, out)?;
                Ok(Value::Pair(Box::new(x), Box::new(y)))
            }
            E::FirstOf(inner) => match self.eval_expr(inner, frame, out)? {
                Value::Pair(x, _) => Ok(*x),
                Value::List(items) => match items.first() {
                    Some(v) => Ok(v.clone()),
                    None => Ok(Value::Missing),
                },
                other => Ok(other),
            },
            E::SecondOf(inner) => match self.eval_expr(inner, frame, out)? {
                Value::Pair(_, y) => Ok(*y),
                other => Ok(other),
            },
            E::JoinedWith(inner, sep) => {
                let v = self.eval_expr(inner, frame, out)?;
                let shown = self.show_value(&v, &SayMods::default());
                let parts: Vec<String> = match v {
                    Value::List(items) => items
                        .iter()
                        .map(|t| self.show_value(t, &SayMods::default()))
                        .collect(),
                    _ => vec![shown],
                };
                Ok(Value::Text(parts.join(sep)))
            }
            E::CollEmpty { kind, size } => match kind {
                sem::Kind::Map(_, _) => Ok(Value::Map(Vec::new())),
                sem::Kind::Set(_) => Ok(Value::Set(Vec::new())),
                sem::Kind::Queue(_) => Ok(Value::Queue(Vec::new())),
                sem::Kind::Array(_) => {
                    let n = size.unwrap_or(0);
                    Ok(Value::Array(vec![None; n]))
                }
                sem::Kind::List(_) => Ok(Value::List(Vec::new())),
                _ => Ok(Value::Missing),
            },
            E::ItemN { list, n } => {
                let l = self.eval_expr(list, frame, out)?;
                let n = as_i64(&self.eval_expr(n, frame, out)?);
                match l {
                    Value::List(items) => item_n_of(&items, n),
                    Value::Array(slots) => {
                        if n < 1 || (n as usize) > slots.len() {
                            return Err(fatal(
                                "T0601",
                                "Item out of range.",
                                "Ask for an item from 1 to N, or use safe item.",
                            ));
                        }
                        match &slots[(n - 1) as usize] {
                            Some(v) => Ok(v.clone()),
                            None => Err(fatal("T0615", "Array item never set.", "Set it first.")),
                        }
                    }
                    other => Ok(other),
                }
            }
            E::SafeItemN { list, n } => {
                let l = self.eval_expr(list, frame, out)?;
                let n = as_i64(&self.eval_expr(n, frame, out)?);
                match l {
                    Value::List(items) => {
                        if n < 1 || (n as usize) > items.len() {
                            Ok(Value::Missing)
                        } else {
                            Ok(items[(n - 1) as usize].clone())
                        }
                    }
                    other => Ok(other),
                }
            }
            E::ItemsRange { list, from, to } => {
                let l = self.eval_expr(list, frame, out)?;
                let a = as_i64(&self.eval_expr(from, frame, out)?);
                let b = as_i64(&self.eval_expr(to, frame, out)?);
                match l {
                    Value::List(items) => {
                        let lo = a.max(1).min(items.len() as i64);
                        let hi = b.max(lo - 1).min(items.len() as i64);
                        Ok(Value::List(items[(lo - 1) as usize..hi as usize].to_vec()))
                    }
                    other => Ok(other),
                }
            }
            E::FirstN { list, n } => {
                let l = self.eval_expr(list, frame, out)?;
                let n = as_i64(&self.eval_expr(n, frame, out)?);
                match l {
                    Value::List(items) => {
                        let k = n.max(0).min(items.len() as i64) as usize;
                        Ok(Value::List(items[..k].to_vec()))
                    }
                    // first N of SEQ works on a generator too: it pulls at
                    // most N items (ch.25, M3-S32)
                    Value::Generator(g) => {
                        let items = self.generator_pull(&g, n.max(0) as usize, frame, out)?;
                        Ok(Value::List(items))
                    }
                    other => Ok(other),
                }
            }
            E::Where { list, cond } => {
                let v = self.eval_expr(list, frame, out)?;
                match v {
                    Value::List(items) => {
                        let mut kept = Vec::new();
                        for it in items {
                            let saved = frame.where_item.take();
                            frame.where_item = Some(it.clone());
                            let yes =
                                matches!(self.eval_expr(cond, frame, out)?, Value::Boolean(true));
                            frame.where_item = saved;
                            if yes {
                                kept.push(it);
                            }
                        }
                        Ok(Value::List(kept))
                    }
                    other => Ok(other),
                }
            }
            E::FirstFib(n) => {
                let n = as_i64(&self.eval_expr(n, frame, out)?);
                let mut items = Vec::new();
                let (mut a, mut b) = (0i64, 1i64);
                for _ in 0..n.max(0) {
                    items.push(Value::Whole(a));
                    let next = a
                        .checked_add(b)
                        .ok_or_else(|| fatal("T0603", T0603_C, T0603_F))?;
                    a = b;
                    b = next;
                }
                Ok(Value::List(items))
            }
            E::PrimesTo(n) => {
                let n = as_i64(&self.eval_expr(n, frame, out)?);
                Ok(Value::List(primes_to(n)))
            }
            E::MinMax { big, items } => {
                // biggest of X and Y and ... (ch.8): the best item by the
                // order of the kind. Records with a can compare impl use it.
                let mut vals = Vec::new();
                for it in items {
                    vals.push(self.eval_expr(it, frame, out)?);
                }
                let Some(first) = vals.first().cloned() else {
                    return Ok(Value::Missing);
                };
                let mut best = first.clone();
                for v in vals.iter().skip(1) {
                    let less = self.cmp_values_less(&best, v, frame, out)?;
                    let take = if *big { less } else { !less };
                    if take {
                        best = v.clone();
                    }
                }
                Ok(best)
            }
            E::AsDyn { value, verb } => {
                let v = self.eval_expr(value, frame, out)?;
                let type_name = match &v {
                    Value::Record(name, _) => name.clone(),
                    Value::Dyn { type_name, .. } => type_name.clone(),
                    other => {
                        let _ = verb;
                        return Err(fatal(
                            "T0323",
                            &format!(
                                "A value of kind {} cannot be used as a dynamic kind.",
                                kind_word_of(other)
                            ),
                            "Only a kind that keeps the promise can convert.",
                        ));
                    }
                };
                Ok(Value::Dyn {
                    type_name,
                    value: Box::new(v),
                })
            }
            E::FnRef(_) => Ok(Value::Missing),
            E::LastOf(inner) => match self.eval_expr(inner, frame, out)? {
                Value::List(items) => match items.last() {
                    Some(v) => Ok(v.clone()),
                    None => Ok(Value::Missing),
                },
                Value::Pair(_, y) => Ok(*y),
                other => Ok(other),
            },
            E::PositionOf { haystack, needle } => {
                let h = self.eval_expr(haystack, frame, out)?;
                // a pattern needle counts from the pattern match (ch.14)
                if let E::PatWords { parts } = &needle.e {
                    return match h {
                        Value::Text(text) => {
                            let pos = pat_find(parts, &text)
                                .map(|(s, _)| graphemes_of(&text[..s]).count() as i64 + 1);
                            Ok(Value::Maybe(pos.map(|p| Box::new(Value::Whole(p)))))
                        }
                        other => Ok(other),
                    };
                }
                let needle = self.eval_expr(needle, frame, out)?;
                match h {
                    Value::List(items) => {
                        let pos = items
                            .iter()
                            .position(|it| cmp_eq(it, &needle))
                            .map(|p| p as i64 + 1);
                        Ok(Value::Maybe(pos.map(|p| Box::new(Value::Whole(p)))))
                    }
                    Value::Text(text) => {
                        let pos = as_text_pos(&text, &needle);
                        Ok(Value::Maybe(pos.map(|p| Box::new(Value::Whole(p)))))
                    }
                    other => Ok(other),
                }
            }
            E::ValueOf { map, key } => match self.eval_expr(&map, frame, out)? {
                Value::Map(entries) => {
                    let key = self.eval_expr(&key, frame, out)?;
                    let v = entries
                        .iter()
                        .find(|(ek, _)| cmp_eq(ek, &key))
                        .map(|(_, v)| v.clone());
                    Ok(Value::Maybe(v.map(|v| Box::new(v))))
                }
                other => Ok(other),
            },
            E::IsEmpty(inner) => match self.eval_expr(inner, frame, out)? {
                Value::List(items) => Ok(Value::Boolean(items.is_empty())),
                Value::Map(entries) => Ok(Value::Boolean(entries.is_empty())),
                Value::Set(items) => Ok(Value::Boolean(items.is_empty())),
                Value::Queue(items) => Ok(Value::Boolean(items.is_empty())),
                Value::Array(slots) => Ok(Value::Boolean(slots.is_empty())),
                Value::Text(t) => Ok(Value::Boolean(t.is_empty())),
                other => Ok(other),
            },
            E::Has { coll, item } => {
                let c = self.eval_expr(coll, frame, out)?;
                let it = self.eval_expr(item, frame, out)?;
                match c {
                    Value::List(items) => Ok(Value::Boolean(items.iter().any(|x| cmp_eq(x, &it)))),
                    Value::Set(items) => Ok(Value::Boolean(items.iter().any(|x| cmp_eq(x, &it)))),
                    Value::Map(entries) => Ok(Value::Boolean(
                        entries.iter().any(|(ek, _)| cmp_eq(ek, &it)),
                    )),
                    other => Ok(other),
                }
            }
            E::Union { a, b } => {
                let sa = self.eval_expr(a, frame, out)?;
                let sb = self.eval_expr(b, frame, out)?;
                match (sa, sb) {
                    (Value::Set(a), Value::Set(b)) => {
                        let mut r: Vec<Value> = a;
                        for x in b {
                            if !r.iter().any(|y| cmp_eq(y, &x)) {
                                r.push(x);
                            }
                        }
                        Ok(Value::Set(r))
                    }
                    (other, _) => Ok(other),
                }
            }
            E::Overlap { a, b } => {
                let sa = self.eval_expr(a, frame, out)?;
                let sb = self.eval_expr(b, frame, out)?;
                match (sa, sb) {
                    (Value::Set(a), Value::Set(b)) => {
                        let r: Vec<Value> = a
                            .into_iter()
                            .filter(|x| b.iter().any(|y| cmp_eq(y, x)))
                            .collect();
                        Ok(Value::Set(r))
                    }
                    (other, _) => Ok(other),
                }
            }
            E::Difference { a, b } => {
                let sa = self.eval_expr(a, frame, out)?;
                let sb = self.eval_expr(b, frame, out)?;
                match (sa, sb) {
                    (Value::Set(a), Value::Set(b)) => {
                        let r: Vec<Value> = a
                            .into_iter()
                            .filter(|x| !b.iter().any(|y| cmp_eq(x, y)))
                            .collect();
                        Ok(Value::Set(r))
                    }
                    (other, _) => Ok(other),
                }
            }
            E::Split { text, sep } => {
                let t = self.eval_expr(text, frame, out)?;
                match t {
                    Value::Text(text) => {
                        // a pattern separator splits at every match (ch.14)
                        if let E::PatWords { parts } = &sep.e {
                            let mut pieces: Vec<Value> = Vec::new();
                            let mut last = 0;
                            for (s, e) in pat_all(parts, &text) {
                                pieces.push(Value::Text(text[last..s].to_string()));
                                last = e;
                            }
                            pieces.push(Value::Text(text[last..].to_string()));
                            return Ok(Value::List(pieces));
                        }
                        let s = self.eval_expr(sep, frame, out)?;
                        // named separators have the names of ch.14
                        let mut sep_s = match s {
                            Value::Text(s) => s,
                            _ => " ".to_string(),
                        };
                        if sep_s == "comma" {
                            sep_s = ",".to_string();
                        } else if sep_s == "space" {
                            sep_s = " ".to_string();
                        } else if sep_s == "newline" {
                            sep_s = "\n".to_string();
                        } else if sep_s == "tab" {
                            sep_s = "\t".to_string();
                        } else if sep_s == "nothing" {
                            sep_s = String::new();
                        }
                        if sep_s.is_empty() {
                            Ok(Value::List(
                                graphemes_of(&text)
                                    .map(|c| Value::Text(c.to_string()))
                                    .collect(),
                            ))
                        } else {
                            Ok(Value::List(
                                text.split(&sep_s)
                                    .map(|p| Value::Text(p.to_string()))
                                    .collect(),
                            ))
                        }
                    }
                    other => Ok(other),
                }
            }
            E::Replace { pat, repl, text } => {
                let t = self.eval_expr(text, frame, out)?;
                let r = self.eval_expr(repl, frame, out)?;
                match t {
                    Value::Text(text) => {
                        let repl_s = match r {
                            Value::Text(s) => s,
                            _ => String::new(),
                        };
                        // a pattern replaces every leftmost, longest match (ch.14)
                        if let E::PatWords { parts } = &pat.e {
                            let mut out_text = String::new();
                            let mut last = 0;
                            for (s, e) in pat_all(parts, &text) {
                                out_text.push_str(&text[last..s]);
                                out_text.push_str(&repl_s);
                                last = e;
                            }
                            out_text.push_str(&text[last..]);
                            return Ok(Value::Text(out_text));
                        }
                        let p = self.eval_expr(pat, frame, out)?;
                        let pat_s = match p {
                            Value::Text(s) => s,
                            _ => String::new(),
                        };
                        Ok(Value::Text(text.replace(&pat_s, &repl_s)))
                    }
                    other => Ok(other),
                }
            }
            E::Neg(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                match v {
                    Value::Whole(x) => x
                        .checked_neg()
                        .map(Value::Whole)
                        .ok_or_else(|| fatal("T0603", T0603_C, T0603_F)),
                    Value::Dec(x) => {
                        if x.is_finite() || x != 0.0 {
                            Ok(Value::Dec(-x))
                        } else {
                            Ok(Value::Dec(-x))
                        }
                    }
                    Value::Text(t) => Ok(Value::Text(format!("minus {t}"))),
                    other => Ok(other),
                }
            }
            E::Binary { op, l, r } => {
                let a = self.eval_expr(l, frame, out)?;
                let b = self.eval_expr(r, frame, out)?;
                bin_op(*op, &a, &b)
            }
            E::DivWhole(l, r) => {
                let a = self.eval_expr(l, frame, out)?;
                let b = self.eval_expr(r, frame, out)?;
                let (x, y) = (as_i64(&a), as_i64(&b));
                if y == 0 {
                    return Err(fatal("T0604", T0604_C, T0604_F));
                }
                Ok(Value::Whole(x / y))
            }
            E::Rem(l, r) => {
                let a = self.eval_expr(l, frame, out)?;
                let b = self.eval_expr(r, frame, out)?;
                let (x, y) = (as_i64(&a), as_i64(&b));
                if y == 0 {
                    return Err(fatal("T0604", T0604_C, T0604_F));
                }
                Ok(Value::Whole(x % y))
            }
            E::Pow(l, r) => {
                let a = self.eval_expr(l, frame, out)?;
                let b = self.eval_expr(r, frame, out)?;
                let (x, y) = (as_i64(&a), as_i64(&b));
                if y < 0 {
                    return Ok(Value::Whole(0));
                }
                let value = if x == 0 {
                    Some(0)
                } else if x == 1 {
                    Some(1)
                } else if x == -1 {
                    Some(if y % 2 == 0 { 1 } else { -1 })
                } else if y > 62 {
                    None
                } else {
                    let mut acc: i64 = 1;
                    let mut failed = false;
                    for _ in 0..y {
                        match acc.checked_mul(x) {
                            Some(v) => acc = v,
                            None => {
                                failed = true;
                                break;
                            }
                        }
                    }
                    if failed { None } else { Some(acc) }
                };
                value
                    .map(Value::Whole)
                    .ok_or_else(|| fatal("T0603", T0603_C, T0603_F))
            }
            E::Round(inner, even) => {
                let v = self.eval_expr(inner, frame, out)?;
                match v {
                    Value::Whole(x) => Ok(Value::Whole(x)),
                    Value::Dec(x) => {
                        if *even {
                            Ok(Value::Whole(x.round_ties_even() as i64))
                        } else {
                            Ok(Value::Whole(x.round() as i64))
                        }
                    }
                    other => Ok(other),
                }
            }
            E::Factorial(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                match v {
                    Value::Whole(n) if n >= 0 => {
                        self.tick()?;
                        Ok(Value::Big(big_factorial(n)))
                    }
                    _ => Err(TErr::Fatal(
                        "Error: A factorial needs a whole number of zero or more.".to_string(),
                    )),
                }
            }
            E::Call { name, args } => self.eval_call(name, args, frame, out),
            E::CountIn(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                Ok(Value::Whole(match &v {
                    Value::Missing => 0,
                    other => count_items(other),
                }))
            }
            E::Lower(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                Ok(Value::Text(as_text(&v).to_lowercase()))
            }
            E::AndOr(l, r, is_and) => {
                let a = self.eval_expr(l, frame, out)?;
                let b = self.eval_expr(r, frame, out)?;
                let (a, b) = (as_truthy(&a), as_truthy(&b));
                Ok(Value::Boolean(if *is_and { a && b } else { a || b }))
            }
            E::AsWhole(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                match v {
                    Value::Whole(_) | Value::Big(_) => Ok(v),
                    _ => Err(not_allowed()),
                }
            }
            E::AsDecimal(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                match v {
                    Value::Whole(x) => Ok(Value::Dec(x as f64)),
                    Value::Big(n) => Ok(Value::Dec(big_to_f64(&n))),
                    c @ Value::Dec(_) => Ok(c),
                    _ => Err(not_allowed()),
                }
            }
            E::AsBig(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                match v {
                    Value::Whole(x) => match big_from_i64(x) {
                        Some(b) => Ok(Value::Big(b)),
                        None => Err(not_allowed()),
                    },
                    Value::Big(b) => Ok(Value::Big(b)),
                    _ => Err(not_allowed()),
                }
            }
            E::AsText(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                // M4-7 (S56): a secret cannot be converted; the hidden
                // print is only for Say (and the log line in M4-9).
                if matches!(v, Value::Secret(_)) {
                    return Err(TErr::Signal);
                }
                Ok(Value::Text(self.show_value(&v, &SayMods::default())))
            }
            E::AsNumber(inner) => {
                let v = self.eval_expr(inner, frame, out)?;
                match &v {
                    Value::Text(t) => match parse_number(t) {
                        Some(n) => Ok(n),
                        None => Err(TErr::Signal),
                    },
                    Value::Whole(_) | Value::Dec(_) => Ok(v.clone()),
                    _ => Err(not_allowed()),
                }
            }
            E::AsMaybe(inner) => {
                // viewing a value as maybe: the value itself, absence stays absent (ch.18)
                self.eval_expr(inner, frame, out)
            }
            E::RecordOf { type_name, parts } => {
                let mut r: Vec<(String, Value)> = Vec::new();
                for (n, e) in parts {
                    let v = self.eval_expr(e, frame, out)?;
                    r.push((n.clone(), v));
                }
                let v = type_name.clone();
                // the Always invariants of the kind run on every value of the
                // kind that is built (ch.64, M3-S38); M3b: conditions proven
                // always true at THIS construction site are skipped, so the
                // site facts go along
                let site = std::ptr::from_ref(e) as usize;
                self.run_always(&v, &r, Some((site, parts.as_slice())), out)?;
                Ok(Value::Record(v, r))
            }
            E::EnumOf { shape, parts } => {
                let mut r: Vec<Value> = Vec::new();
                for (_, e) in parts {
                    let v = self.eval_expr(e, frame, out)?;
                    r.push(v);
                }
                Ok(Value::Enum {
                    variant: shape.clone(),
                    parts: r,
                })
            }
            E::PartOf {
                type_name,
                part,
                base,
            } => {
                let v = self.eval_expr(base, frame, out)?;
                part_of_value(&v, part, type_name)
            }
            E::CopyOf(inner) => {
                // copy of X: an owned copy of the value (ch.20)
                self.eval_expr(inner, frame, out)
            }
            E::Move(inner) => {
                // give X: the move is enforced at compile time; at run time it
                // is just the value (ch.28)
                self.eval_expr(inner, frame, out)
            }
            E::Share(inner) => {
                // share X: a counted handle to the value (ch.28)
                let v = self.eval_expr(inner, frame, out)?;
                Ok(Value::Share(Box::new(v)))
            }
            E::WeakShare(inner) => {
                // weak share X: a non-owning link; reading it once the owner is
                // gone gives missing (ch.28, M2-S44)
                let _ = self.eval_expr(inner, frame, out)?;
                Ok(Value::Missing)
            }
            // ---- M4 (Appendix K): channel, guarded, atomic, counter ----
            E::ChannelOf { item, cap } => {
                // channel of T [holding N] (M4-G7): both ends in the one
                // value (M4-S15); the Rc shares the state across copies.
                Ok(Value::Channel(std::rc::Rc::new(std::cell::RefCell::new(
                    sem::ChannelState {
                        queue: Vec::new(),
                        cap: *cap,
                        item: Some(item.clone()),
                        closed: false,
                    },
                ))))
            }
            E::GuardedOf(inner) => {
                // guarded V (M4-G8): a cell holding V (M4-S16)
                let v = self.eval_expr(inner, frame, out)?;
                Ok(Value::Guarded(Box::new(v)))
            }
            E::AtomicNum => Ok(Value::Atomic(0)), // M4-S19: starts at 0
            E::CounterZero => Ok(Value::Counter(0)), // M4-S20: starts at 0
            E::FileExists(f) => {
                // M4-G45: a yes-or-no question about a path (a folder is
                // asked about like a file)
                let path = self.resolve_file(f, frame)?;
                Ok(Value::Boolean(std::fs::symlink_metadata(&path).is_ok()))
            }
            E::JsonOf(inner) => {
                // M4-6 (S46): json of x is the compact json text of the
                // value; a value json does not hold fails the ordinary
                // way (logged with the format cuts)
                let v = self.eval_expr(inner, frame, out)?;
                let text = crate::formats::json_compact(&v).map_err(|_| TErr::Signal)?;
                Ok(Value::Text(text))
            }
            // ---- M4-10 (Appendix K 7.8): the request read rows (G77) ----
            E::RequestRead { row } => {
                let Some(ctx) = &self.handler_ctx else {
                    return Err(fatal(
                        "T0113",
                        "A request read runs outside a handler.",
                        "The reads of request belong in a When someone block.",
                    ));
                };
                match row {
                    sem::RequestRow::Method => Ok(Value::Text(ctx.method.to_ascii_lowercase())),
                    sem::RequestRow::Page => Ok(Value::Text(ctx.page.clone())),
                    sem::RequestRow::Text => {
                        Ok(Value::Text(String::from_utf8_lossy(&ctx.body).to_string()))
                    }
                    sem::RequestRow::Data => Ok(Value::List(
                        ctx.body.iter().map(|b| Value::Whole(*b as i64)).collect(),
                    )),
                    sem::RequestRow::Header(name) => Ok(ctx
                        .headers
                        .iter()
                        .find(|(k, _)| k == &name.to_ascii_lowercase())
                        .map(|(_, v)| Value::Text(v.clone()))
                        .unwrap_or(Value::Missing)),
                    sem::RequestRow::Query(name) => Ok(ctx
                        .query
                        .iter()
                        .find(|(k, _)| k == name)
                        .map(|(_, v)| Value::Text(v.clone()))
                        .unwrap_or(Value::Missing)),
                    sem::RequestRow::Parameter(name) => Ok(ctx
                        .params
                        .iter()
                        .find(|(k, _)| k == name)
                        .map(|(_, v)| Value::Text(v.clone()))
                        .unwrap_or(Value::Missing)),
                }
            }
            E::Flat(pieces) => {
                let mut parts: Vec<String> = Vec::new();
                for p in pieces {
                    let v = self.eval_expr(p, frame, out)?;
                    parts.push(self.show_value(&v, &SayMods::default()));
                }
                Ok(Value::Text(parts.join(" ")))
            }
            E::Compare(c) => {
                let l = self.eval_expr(&c.l, frame, out)?;
                let mut r: Vec<Value> = Vec::new();
                for x in &c.r {
                    r.push(self.eval_expr(x, frame, out)?);
                }
                // M4-7 (S56): a secret cannot be compared. Every
                // comparison sentence refuses anonymously when a secret
                // is one side (collection membership is the logged cut:
                // the derived equality compares through there).
                if matches!(l, Value::Secret(_)) || r.iter().any(|x| matches!(x, Value::Secret(_)))
                {
                    return Err(TErr::Signal);
                }
                let raw = match c.rel {
                    Rel::Equal => cmp_eq(&l, &r[0]),
                    Rel::Not => !cmp_eq(&l, &r[0]),
                    // Ordered questions ask the kind's can compare impl
                    // first (ch.26, M3-S19); built-in kinds fall through to
                    // the plain order inside cmp_values_less.
                    Rel::Less => self.cmp_values_less(&l, &r[0], frame, out)?,
                    Rel::More => self.cmp_values_less(&r[0], &l, frame, out)?,
                    Rel::AtLeast => !self.cmp_values_less(&l, &r[0], frame, out)?,
                    Rel::AtMost => !self.cmp_values_less(&r[0], &l, frame, out)?,
                    Rel::Close => cmp_close(&l, &r[0]),
                    Rel::Between => {
                        let lo = cmp_ord(&l, &r[0])? != std::cmp::Ordering::Less;
                        let hi = cmp_ord(&l, &r[1])? != std::cmp::Ordering::Greater;
                        lo && hi
                    }
                    Rel::IsEmpty => match &l {
                        Value::List(items) => items.is_empty(),
                        Value::Map(entries) => entries.is_empty(),
                        Value::Set(items) => items.is_empty(),
                        Value::Queue(items) => items.is_empty(),
                        Value::Array(slots) => slots.is_empty(),
                        Value::Text(t) => t.is_empty(),
                        _ => false,
                    },
                    Rel::Has => {
                        let item = &r[0];
                        match &l {
                            Value::List(items) => items.iter().any(|x| cmp_eq(x, item)),
                            Value::Set(items) => items.iter().any(|x| cmp_eq(x, item)),
                            Value::Map(entries) => entries.iter().any(|(ek, _)| cmp_eq(ek, item)),
                            _ => false,
                        }
                    }
                    Rel::Missing => is_missing_like(&l),
                    Rel::There => !is_missing_like(&l),
                };
                Ok(Value::Boolean(raw != c.negate))
            }
            // ---- M4-7 (Appendix K 7.7): time, random, secrets ---------
            // The arms live in eval_m47, their own function frame: the
            // evaluator recursion (a call per program function) already
            // runs near the thread stack limit, and these arms must not
            // grow eval_expr's frame.
            E::DateCtor { .. }
            | E::Today
            | E::Now
            | E::MomentAt { .. }
            | E::InZone { .. }
            | E::TimeShift { .. }
            | E::DurationOf { .. }
            | E::DaysBetween { .. }
            | E::SecondsBetween { .. }
            | E::RandomRange { .. }
            | E::RandomDec
            | E::RandomItem { .. }
            | E::Shuffled { .. }
            | E::HashOf(_)
            | E::SecretOf(_)
            | E::Reveal(_) => {
                return self.eval_m47(&e.e, frame, out);
            }
            // ---- M4-8 (Appendix K 7.10/7.11): environment, input -------
            // Same frame-size rule as the M4-7 arms above.
            E::Environment { .. } | E::ReadInput => {
                return self.eval_m48(&e.e, frame, out);
            }
        }
    }

    /// The M4-8 (Appendix K 7.10/7.11) environment and input reads. A
    /// separate (non-inlined) function so the deep evaluator recursion
    /// does not carry these locals in every frame.
    #[inline(never)]
    fn eval_m48(&mut self, e: &sem::E, frame: &mut Frame, out: &mut String) -> R<Value> {
        match e {
            sem::E::Environment { name } => {
                // M4-G24/S80: the variable named by the words in upper
                // case joined by _ (Lykaon_MODE); the value is maybe text
                // (missing when the variable is not set). The permission
                // Allows environment is not gated yet (logged: the
                // permission system lands with its milestone).
                match std::env::var(name) {
                    Ok(v) => Ok(Value::Maybe(Some(Box::new(Value::Text(v))))),
                    Err(_) => Ok(Value::Maybe(None)),
                }
            }
            sem::E::ReadInput => {
                // M4-S85: all of standard input as text (the runners read
                // it once; this is the buffered text).
                let _ = frame;
                let _ = out;
                Ok(Value::Text(self.input.clone()))
            }
            _ => unreachable!("eval_m48 holds only the M4-8 arms"),
        }
    }

    /// The M4-7 (Appendix K 7.7) time, random and secret reads. A
    /// separate (non-inlined) function so the deep evaluator recursion
    /// does not carry these locals in every frame.
    #[inline(never)]
    fn eval_m47(&mut self, e: &sem::E, frame: &mut Frame, out: &mut String) -> R<Value> {
        match e {
            E::DateCtor { y, m, d } => {
                // M4-G54: date N and N and N. The numbers are literals
                // and the compile check refuses an impossible date with
                // T0620, so the runtime arm only rebuilds the value.
                Ok(Value::Date(*y, *m, *d))
            }
            E::Today => {
                // M4-G54: today is the date in the local zone.
                let (y, m, d) = crate::time4::today_ymd();
                Ok(Value::Date(y, m, d))
            }
            E::Now => {
                // M4-G55: now is the instant in the local zone.
                Ok(Value::Moment {
                    nanos: crate::time4::now_nanos(),
                    zone: crate::time4::local_zone_name(),
                })
            }
            E::MomentAt { date, h, m } => {
                // M4-G55: moment of D at H and M is H:M:00 on date D in
                // the local zone. The hour and minute are literals
                // (range-checked at compile, T0620 family); the date
                // operand is a runtime value here.
                let v = self.eval_expr(date, frame, out)?;
                let Value::Date(y, mth, d) = v else {
                    return Err(TErr::Signal);
                };
                let Some(nanos) = crate::time4::local_moment_nanos(y, mth, d, *h, *m) else {
                    return Err(TErr::Signal);
                };
                Ok(Value::Moment {
                    nanos,
                    zone: crate::time4::local_zone_name(),
                })
            }
            E::InZone { base, zone } => {
                // M4-G55: M in zone asia dhaka converts. The same
                // instant, another IANA zone. The zone words are
                // literals: the compile check refuses a name no IANA
                // zone matches with T0171, so a runtime miss stays the
                // anonymous failure.
                let v = self.eval_expr(base, frame, out)?;
                let Value::Moment { nanos, .. } = v else {
                    return Err(TErr::Signal);
                };
                let Some(name) = crate::time4::find_zone(zone) else {
                    return Err(TErr::Signal);
                };
                Ok(Value::Moment { nanos, zone: name })
            }
            E::TimeShift {
                n,
                unit,
                before,
                base,
            } => {
                // M4-G56: N unit after/before X. Calendar rules for
                // dates (days; a week is 7 calendar days), exact length
                // for moments; the other units on a date are the wrong
                // shape (logged). Months and years are not units.
                let v = self.eval_expr(base, frame, out)?;
                let sign: i128 = if *before { -1 } else { 1 };
                let amount = *n as i128;
                match (&v, unit.as_str()) {
                    (Value::Date(y, m, d), "days" | "weeks") => {
                        let days: i64 = if unit == "weeks" { *n * 7 } else { *n };
                        let s: i64 = if *before { -1 } else { 1 };
                        let nd = crate::time4::days_from_civil(*y, *m, *d).checked_add(s * days);
                        let Some(nd) = nd else {
                            return Err(TErr::Signal);
                        };
                        let (y2, m2, d2) = crate::time4::civil_from_days(nd);
                        if !(-9999..=9999).contains(&y2) {
                            return Err(TErr::Signal);
                        }
                        Ok(Value::Date(y2, m2, d2))
                    }
                    (Value::Moment { nanos, zone }, _) => {
                        let unit_nanos: i128 = match unit.as_str() {
                            "milliseconds" => 1_000_000,
                            "seconds" => 1_000_000_000,
                            "minutes" => 60_000_000_000,
                            "hours" => 3_600_000_000_000,
                            "days" => 86_400_000_000_000,
                            "weeks" => 604_800_000_000_000,
                            _ => return Err(TErr::Signal),
                        };
                        let shift = sign
                            .checked_mul(amount)
                            .and_then(|s| s.checked_mul(unit_nanos));
                        let Some(shift) = shift else {
                            return Err(TErr::Signal);
                        };
                        let Some(new) = nanos.checked_add(shift) else {
                            return Err(TErr::Signal);
                        };
                        Ok(Value::Moment {
                            nanos: new,
                            zone: zone.clone(),
                        })
                    }
                    _ => Err(TErr::Signal),
                }
            }
            E::DurationOf { nanos } => {
                // M4-S52/G5: NUMBER time_unit such as 5 seconds is a
                // duration (nanoseconds). The literal is non-negative;
                // a negative length is a logged cut (before is the
                // negative direction in the time shifts).
                Ok(Value::Duration(*nanos))
            }
            E::DaysBetween { a, b } => {
                // M4-G56: days between X and Y (calendar days).
                let va = self.eval_expr(a, frame, out)?;
                let vb = self.eval_expr(b, frame, out)?;
                match (va, vb) {
                    (Value::Date(y1, m1, d1), Value::Date(y2, m2, d2)) => {
                        let n1 = crate::time4::days_from_civil(y1, m1, d1);
                        let n2 = crate::time4::days_from_civil(y2, m2, d2);
                        match n2.checked_sub(n1).and_then(|d| i64::try_from(d).ok()) {
                            Some(d) => Ok(Value::Whole(d)),
                            None => Err(TErr::Signal),
                        }
                    }
                    _ => Err(TErr::Signal),
                }
            }
            E::SecondsBetween { a, b } => {
                // M4-G56: seconds between X and Y (exact seconds;
                // leftover nanoseconds truncate toward zero - logged).
                let va = self.eval_expr(a, frame, out)?;
                let vb = self.eval_expr(b, frame, out)?;
                match (va, vb) {
                    (Value::Moment { nanos: n1, .. }, Value::Moment { nanos: n2, .. }) => {
                        match n2.checked_sub(n1) {
                            Some(d) => match i64::try_from(d / 1_000_000_000) {
                                Ok(s) => Ok(Value::Whole(s)),
                                Err(_) => Err(TErr::Signal),
                            },
                            None => Err(TErr::Signal),
                        }
                    }
                    _ => Err(TErr::Signal),
                }
            }
            E::RandomRange { a, b } => {
                // M4-S54: uniform over both ends. The ends are whole
                // numbers (a decimal end fails the anonymous way -
                // logged); a reversed range fails too.
                let va = self.eval_expr(a, frame, out)?;
                let vb = self.eval_expr(b, frame, out)?;
                let (Value::Whole(lo), Value::Whole(hi)) = (va, vb) else {
                    return Err(TErr::Signal);
                };
                if hi < lo {
                    return Err(TErr::Signal);
                }
                let count = (hi as i128 - lo as i128 + 1) as u128;
                // two 64-bit draws over a 128-bit modulo keep the bias
                // far below anything observable
                let hi64 = self.rng_next() as u128;
                let lo64 = self.rng_next() as u128;
                let pick = ((hi64 << 64) | lo64) % count;
                Ok(Value::Whole(lo + pick as i64))
            }
            E::RandomDec => {
                // M4-S54: a decimal in [0, 1), 53 random bits (logged).
                let bits = self.rng_next() >> 11;
                Ok(Value::Dec(bits as f64 * (1.0f64 / 9_007_199_254_740_992.0)))
            }
            E::RandomItem { list } => {
                // M4-S54/G57: one item of the collection at random; an
                // empty collection fails the anonymous way.
                let v = self.eval_expr(list, frame, out)?;
                let items = match v {
                    Value::List(items) | Value::Set(items) | Value::Queue(items) => items,
                    _ => return Err(TErr::Signal),
                };
                if items.is_empty() {
                    return Err(TErr::Signal);
                }
                let i = (self.rng_next() % items.len() as u64) as usize;
                Ok(items[i].clone())
            }
            E::Shuffled { list } => {
                // M4-S54/G57: the Fisher-Yates method; a new list.
                let v = self.eval_expr(list, frame, out)?;
                let mut items = match v {
                    Value::List(items) | Value::Set(items) | Value::Queue(items) => items,
                    _ => return Err(TErr::Signal),
                };
                for i in (1..items.len()).rev() {
                    let j = (self.rng_next() % (i as u64 + 1)) as usize;
                    items.swap(i, j);
                }
                Ok(Value::List(items))
            }
            E::HashOf(x) => {
                // M4-S55: the SHA-256 of the UTF-8 bytes of the text, or
                // of the bytes. There is no bytes kind in this cut, so a
                // list of whole numbers 0..255 reads as the bytes
                // (logged).
                let v = self.eval_expr(x, frame, out)?;
                let bytes = match v {
                    Value::Text(t) => t.into_bytes(),
                    Value::List(items) => {
                        let mut bytes = Vec::with_capacity(items.len());
                        for it in items {
                            match it {
                                Value::Whole(n) if (0..=255).contains(&n) => {
                                    bytes.push(n as u8);
                                }
                                _ => return Err(TErr::Signal),
                            }
                        }
                        bytes
                    }
                    _ => return Err(TErr::Signal),
                };
                Ok(Value::Text(crate::time4::sha256_hex(&bytes)))
            }
            E::SecretOf(x) => {
                // M4-G60: secret X. The secret holds text in this cut
                // (bytes are not values yet - logged).
                let v = self.eval_expr(x, frame, out)?;
                match v {
                    Value::Text(_) => Ok(Value::Secret(Box::new(crate::sem::SecretInner(v)))),
                    _ => Err(TErr::Signal),
                }
            }
            E::Reveal(x) => {
                // M4-G61: reveal x gives the text (or bytes) of a
                // secret. Reveal of a non-secret fails anonymously.
                let v = self.eval_expr(x, frame, out)?;
                match v {
                    Value::Secret(inner) => Ok(inner.0.clone()),
                    _ => Err(TErr::Signal),
                }
            }
            _ => unreachable!("eval_m47 holds only the M4-7 arms"),
        }
    }

    fn eval_call(
        &mut self,
        name: &str,
        args: &[sem::Expr],
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Value> {
        // A Pretend override (ch.38) short-circuits the call.
        if let Some(v) = self.pretend.get(name) {
            return Ok(v.clone());
        }
        let mut values = Vec::new();
        for a in args {
            values.push(self.eval_expr(a, frame, out)?);
        }
        self.eval_call_values(name, &values, frame, out)
    }

    fn eval_call_values(
        &mut self,
        name: &str,
        values: &[Value],
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Value> {
        // A closure of that name in scope is called (M3-S21). The closure
        // value carries the names it captured where it was written.
        if let Some(Value::Closure { .. }) = frame.find(name) {
            let Some(Value::Closure { func, captures }) = frame.find(name).cloned() else {
                return Ok(Value::Missing);
            };
            return self.eval_closure(&func, captures, values, frame, out);
        }
        // An interface function on a record or dynamic value dispatches to
        // the impl of the value's kind (ch.23, M3-S18).
        if !values.is_empty() {
            if let Some(v) = self.eval_interface_call(name, values, frame, out)? {
                return Ok(v);
            }
        }
        let Some(fdef) = self.prog.funcs.iter().find(|f| f.name == name).cloned() else {
            return Ok(Value::Missing);
        };
        // A generator call gives a lazy sequence (ch.25, M3-S31).
        if fdef.is_generator {
            let args: Vec<(String, Value)> = fdef
                .inputs
                .iter()
                .zip(values)
                .map(|((n, _), v)| (n.clone(), v.clone()))
                .collect();
            // Captured names freeze at creation (M3-D2 snapshot rule), so
            // every replay of the body sees the same captured values.
            let caps: Vec<(String, Value)> = fdef
                .captures
                .iter()
                .filter_map(|c| frame.find(c).map(|v| (c.clone(), v.clone())))
                .collect();
            let (mir, entry) = crate::mir::build_fn_body(&fdef);
            return Ok(Value::Generator(sem::GeneratorHandle::new(
                name.to_string(),
                args,
                std::sync::Arc::new(std::sync::Mutex::new(Vec::new())),
                std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false)),
                std::sync::Arc::new(mir),
                entry,
                caps,
            )));
        }
        self.run_fn_body(&fdef, name, values, frame, out)
    }

    /// Whether the function's `idx`-th Ensures contract is proven always
    /// true by the prover hook (M3b pass 1). Unproven contracts (and any
    /// missing verdict) keep the run-time check.
    fn ensures_proven(&self, fdef: &sem::FuncDef, idx: usize) -> bool {
        let Some(hook) = self.prover else {
            return false;
        };
        let key = (fdef as *const _ as usize, fdef.name.clone());
        let mut map = self.proven.borrow_mut();
        map.entry(key)
            .or_insert_with(|| hook(fdef))
            .get(idx)
            .copied()
            .unwrap_or(false)
    }

    /// Run one Lykaon function instance with `values` as its inputs.
    fn run_fn_body(
        &mut self,
        fdef: &sem::FuncDef,
        name: &str,
        values: &[Value],
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Value> {
        let (inputs, body, default_last, requires, ensures) = (
            &fdef.inputs,
            &fdef.body,
            &fdef.default_last,
            &fdef.requires[..],
            &fdef.ensures[..],
        );
        if values.len() != inputs.len() {
            // one missing LAST input is filled by defaulting to (Ch.15)
            if values.len() + 1 == inputs.len() {
                if let Some(d) = default_last {
                    let dv = self.eval_expr(d, frame, out)?;
                    let mut vals2 = values.to_vec();
                    vals2.push(dv);
                    return self.call_named(name, &vals2, frame, out);
                }
            }
            return Err(fatal(
                "T0126",
                "A call gives more or fewer inputs than the function has.",
                "Match the inputs of the function.",
            ));
        }
        // Calls nested too deep ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Â ÃƒÂ¢Ã¢â€šÂ¬Ã¢â€žÂ¢ÃƒÆ’Ã†â€™ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬Ãƒâ€¦Ã‚Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã†â€™ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬Ãƒâ€¦Ã‚Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬Ãƒâ€¦Ã‚Â¾ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ T0607.
        self.depth += 1;
        if self.depth > 240 {
            self.depth -= 1;
            return Err(fatal("T0607", T0607_C, T0607_F));
        }
        let mut fr = Frame {
            scopes: Vec::new(),
            counters: Vec::new(),
            last_result: None,
            last_shown: String::new(),
            where_item: None,
            tasks: HashMap::new(),
            timers: Vec::new(),
            watchers: Vec::new(),
        };
        let mut sc = ScopeFrame::default();
        for (i, (n, _)) in inputs.iter().enumerate() {
            sc.vars.insert(n.clone(), values[i].clone());
            sc.order.push(n.clone());
        }
        // M3-D2: the call frame sees the fixed names captured where the
        // function was written (seeded from the caller's frame). Impl methods
        // called through eval_interface_call are not in prog.funcs.
        let captures = self
            .prog
            .funcs
            .iter()
            .find(|f| f.name == name)
            .map(|f| f.captures.clone())
            .unwrap_or_default();
        for cap in &captures {
            if let Some(v) = frame.find(cap) {
                sc.vars.insert(cap.to_string(), v.clone());
            }
        }
        fr.scopes.push(sc);
        // Check Requires contracts before executing the body (ch.64, M3-S35).
        for contract in requires {
            let cond_val = self.eval_expr(&contract.cond, &mut fr, out)?;
            if !is_truthy(&cond_val) {
                self.depth -= 1;
                if let Some(scope) = fr.scopes.pop() {
                    let _ = self.run_cleanups(scope, out);
                }
                return Err(fatal(
                    "T0602",
                    &format!("Requires failed: {}", contract.text),
                    &format!("The requires condition '{}' is not met.", contract.text),
                ));
            }
        }
        let result = match body {
            sem::FnBody::Expr(expr) => self.eval_expr(expr, &mut fr, out),
            sem::FnBody::Block(stmts) => match self.exec_stmts(stmts, &mut fr, out) {
                Ok(Flow::Back(_v, failed)) if failed => Err(TErr::Signal),
                Ok(Flow::Back(v, _)) => Ok(v),
                Ok(_) => Ok(Value::Missing),
                Err(e) => Err(e),
            },
        };
        // Check Ensures contracts after successful execution (ch.64, M3-S35).
        match &result {
            Ok(v) => {
                for (idx, contract) in ensures.iter().enumerate() {
                    // M3b pass 1: a contract PROVEN always true by the prover
                    // is skipped; unproven ones keep checking.
                    if self.ensures_proven(fdef, idx) {
                        continue;
                    }
                    let mut fr_ensures = fr.clone();
                    fr_ensures.define("result", v.clone());
                    let cond_val = self.eval_expr(&contract.cond, &mut fr_ensures, out)?;
                    if !is_truthy(&cond_val) {
                        self.depth -= 1;
                        if let Some(scope) = fr.scopes.pop() {
                            let _ = self.run_cleanups(scope, out);
                        }
                        return Err(fatal(
                            "T0602",
                            &format!("Ensures failed: {}", contract.text),
                            &format!("The ensures condition '{}' is not met.", contract.text),
                        ));
                    }
                }
            }
            Err(_) => {}
        }
        if std::env::var("Lykaon_DEBUG").is_ok() {
            let tag = match &result {
                Ok(v) => format!("ok {v:?}"),
                Err(_) => "err".to_string(),
            };
            eprintln!("DBG eval_call {name} {:?} -> {tag}", values);
        }
        self.depth -= 1;
        // Clean up the call's own scope (ch.31, M3-S29).
        if let Some(scope) = fr.scopes.pop() {
            let _ = self.run_cleanups(scope, out);
        }
        result
    }

    /// Re-dispatch by name (used after a defaulting-to fills the last input).
    fn call_named(
        &mut self,
        name: &str,
        values: &[Value],
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Value> {
        let Some(fdef) = self.prog.funcs.iter().find(|f| f.name == name).cloned() else {
            return Ok(Value::Missing);
        };
        self.run_fn_body(&fdef, name, values, frame, out)
    }

    /// Call a closure value: a fresh frame over the captures, then the
    /// function's inputs (M3-D2). Captures not already snapshotted are taken
    /// from the caller's frame (shared borrow, live).
    fn eval_closure(
        &mut self,
        func: &str,
        captures: Vec<(String, Value)>,
        values: &[Value],
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Value> {
        let Some(fdef) = self.prog.funcs.iter().find(|f| f.name == func).cloned() else {
            return Ok(Value::Missing);
        };
        self.depth += 1;
        if self.depth > 240 {
            self.depth -= 1;
            return Err(fatal("T0607", T0607_C, T0607_F));
        }
        let mut fr = Frame {
            scopes: Vec::new(),
            counters: Vec::new(),
            last_result: None,
            last_shown: String::new(),
            where_item: None,
            tasks: HashMap::new(),
            timers: Vec::new(),
            watchers: Vec::new(),
        };
        let mut sc = ScopeFrame::default();
        for (n, v) in captures {
            sc.vars.insert(n.clone(), v);
            sc.order.push(n);
        }
        // shared borrow: names captured but not snapshotted come from the
        // caller's frame at call time
        for cap in &fdef.captures {
            if !sc.vars.contains_key(cap) {
                if let Some(v) = frame.find(cap) {
                    sc.vars.insert(cap.to_string(), v.clone());
                    sc.order.push(cap.to_string());
                }
            }
        }
        for (i, (n, _)) in fdef.inputs.iter().enumerate() {
            sc.vars
                .insert(n.clone(), values.get(i).cloned().unwrap_or(Value::Missing));
            sc.order.push(n.clone());
        }
        fr.scopes.push(sc);
        let result = match &fdef.body {
            sem::FnBody::Expr(expr) => self.eval_expr(&expr, &mut fr, out),
            sem::FnBody::Block(stmts) => match self.exec_stmts(&stmts, &mut fr, out) {
                Ok(Flow::Back(_v, failed)) if failed => Err(TErr::Signal),
                Ok(Flow::Back(v, _)) => Ok(v),
                Ok(_) => Ok(Value::Missing),
                Err(e) => Err(e),
            },
        };
        self.depth -= 1;
        // Clean up the closure's scope (ch.31, M3-S29).
        if let Some(scope) = fr.scopes.pop() {
            let _ = self.run_cleanups(scope, out);
        }
        result
    }

    /// Dispatch `speak rex` / `speak any speaker` to the impl of the value's
    /// kind (ch.23, M3-S18). Returns None when `name` is not an interface
    /// function, so the normal call path continues.
    fn eval_interface_call(
        &mut self,
        name: &str,
        values: &[Value],
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Option<Value>> {
        let iface = self
            .prog
            .interfaces
            .iter()
            .find(|i| i.fn_name == name)
            .cloned();
        let Some(iface) = iface else { return Ok(None) };
        let first = &values[0];
        let type_name = match first {
            Value::Record(t, _) => Some(t.clone()),
            Value::Dyn { type_name, .. } => Some(type_name.clone()),
            _ => None,
        };
        let Some(type_name) = type_name else {
            // not a value of a kind with impls: the default may still answer
            return match &iface.default {
                Some(d) => Ok(Some(Value::Text(d.clone()))),
                None => Err(fatal(
                    "T0325",
                    &format!(
                        "{} does not keep the promise of {}.",
                        kind_word_of(first),
                        iface.verb
                    ),
                    "Give the kind an impl block.",
                )),
            };
        };
        let impl_fn = self
            .prog
            .impls
            .iter()
            .find(|i| i.kind_name == type_name && i.verb == iface.verb && i.meaning.is_none())
            .and_then(|i| i.funcs.iter().find(|f| f.name == iface.fn_name).cloned());
        match impl_fn {
            Some(fdef) => {
                let v = self.run_fn_body(&fdef, name, values, frame, out)?;
                Ok(Some(v))
            }
            None => match &iface.default {
                Some(d) => Ok(Some(Value::Text(d.clone()))),
                None => Err(fatal(
                    "T0325",
                    &format!(
                        "A {type_name} has no {name} although it can {}.",
                        iface.verb
                    ),
                    "Give the kind an impl block, or use the default.",
                )),
            },
        }
    }

    /// Is `a` less than `b`, using a can compare impl when the kinds have
    /// one (ch.26, M3-S19), else the built-in order.
    fn cmp_values_less(
        &mut self,
        a: &Value,
        b: &Value,
        frame: &mut Frame,
        out: &mut String,
    ) -> R<bool> {
        let type_name = match (a, b) {
            (Value::Record(t, _), Value::Record(_, _)) => Some(t.clone()),
            _ => None,
        };
        if let Some(t) = type_name {
            let impl_cmp = self
                .prog
                .impls
                .iter()
                .find(|i| i.kind_name == *t && i.meaning == Some(Meaning::Compare))
                .map(|i| (i.body.clone(), i.line));
            if let Some((body, _line)) = impl_cmp {
                // the impl body answers with yes/no for left and right
                let mut fr = Frame {
                    scopes: Vec::new(),
                    counters: Vec::new(),
                    last_result: None,
                    last_shown: String::new(),
                    where_item: None,
                    tasks: HashMap::new(),
                    timers: Vec::new(),
                    watchers: Vec::new(),
                };
                let mut sc = ScopeFrame::default();
                sc.vars.insert("left".to_string(), a.clone());
                sc.vars.insert("right".to_string(), b.clone());
                sc.vars.insert(t.clone(), a.clone());
                sc.order.push("left".to_string());
                sc.order.push("right".to_string());
                sc.order.push(t);
                fr.scopes.push(sc);
                let sink = &mut String::new();
                return match self.exec_stmts(&body, &mut fr, sink) {
                    Ok(Flow::Back(v, _)) | Ok(Flow::Hand(v)) => Ok(as_truthy(&v)),
                    Ok(_) => Ok(false),
                    Err(TErr::Signal) => Ok(false),
                    Err(e) => Err(e),
                };
            }
        }
        Ok(matches!(cmp_ord(a, b)?, std::cmp::Ordering::Less))
    }

    /// Pull items from a generator handle up to `n` (ch.25, M3-S32). The
    /// body suspends at each Hand back (M3-D12): each pull resumes the saved
    /// block-graph position and frozen frame and runs until the next Hand
    /// back (or until the body ends, marking `finished`); every item lands
    /// in the cache, so later pulls need no new run. Built-in sequences
    /// (first N fibonacci / primes) are lazy at their own expression kind.
    fn generator_pull(
        &mut self,
        g: &sem::GeneratorHandle,
        n: usize,
        frame: &mut Frame,
        out: &mut String,
    ) -> R<Vec<Value>> {
        loop {
            {
                let cache = g.cache.lock().unwrap();
                if g.finished.load(std::sync::atomic::Ordering::Relaxed) || cache.len() >= n {
                    let k = n.min(cache.len());
                    return Ok(cache[..k].to_vec());
                }
            }
            let more = self.gen_run_phase(g, frame, out)?;
            if !more {
                g.finished.store(true, std::sync::atomic::Ordering::Relaxed);
            }
        }
    }

    /// Run one suspension phase of the generator body: up to the next Hand
    /// back (one item appended to the cache) or the end of the body. Returns
    /// whether the body can still hand back more items.
    fn gen_run_phase(
        &mut self,
        g: &sem::GeneratorHandle,
        caller_frame: &mut Frame,
        out: &mut String,
    ) -> R<bool> {
        let Some(fdef) = self.prog.funcs.iter().find(|f| f.name == g.func) else {
            return Ok(false);
        };
        if !gen_resume_safe(&fdef.body) {
            return self.gen_collect_all(g, &fdef.clone(), caller_frame, out);
        }
        let fdef = fdef.clone();
        let reentrant = {
            let mut shared = g.resume.lock().unwrap();
            let r = shared.pull_active;
            if !r {
                shared.pull_active = true;
            }
            r
        };
        if reentrant {
            // A pull of a generator already being pulled: collect the whole
            // body again without suspending (the pre-suspension behavior).
            return self.gen_collect_all(g, &fdef, caller_frame, out);
        }
        let result = self.gen_run_until_hand(g, &fdef, out);
        {
            let mut shared = g.resume.lock().unwrap();
            shared.pull_active = false;
            if matches!(result, Err(_)) {
                // a failed body restarts from the top on the next pull
                *shared = sem::GenState::default();
            }
        }
        result
    }

    /// Suspend-free collect-all run (the pre-M3-D12 behavior, kept for
    /// bodies whose Hand back sits in a nested execution).
    fn gen_collect_all(
        &mut self,
        g: &sem::GeneratorHandle,
        fdef: &sem::FuncDef,
        caller_frame: &mut Frame,
        out: &mut String,
    ) -> R<bool> {
        let mut fr = Frame {
            scopes: Vec::new(),
            counters: Vec::new(),
            last_result: None,
            last_shown: String::new(),
            where_item: None,
            tasks: HashMap::new(),
            timers: Vec::new(),
            watchers: Vec::new(),
        };
        let mut sc = ScopeFrame::default();
        for (i, (n2, _)) in fdef.inputs.iter().enumerate() {
            sc.vars.insert(
                n2.clone(),
                g.args
                    .get(i)
                    .map(|(_, v)| v.clone())
                    .unwrap_or(Value::Missing),
            );
            sc.order.push(n2.clone());
        }
        for cap in &fdef.captures {
            if let Some(v) = caller_frame.find(cap) {
                sc.vars.insert(cap.clone(), v.clone());
                sc.order.push(cap.clone());
            }
        }
        fr.scopes.push(sc);
        let mut sink = String::new();
        self.depth += 1;
        if self.depth > 240 {
            self.depth -= 1;
            return Err(fatal("T0607", T0607_C, T0607_F));
        }
        self.in_generator = true;
        self.pending_hands.clear();
        let run = match &fdef.body {
            sem::FnBody::Expr(_) => Ok(Flow::Normal),
            sem::FnBody::Block(stmts) => self.exec_stmts(&stmts, &mut fr, &mut sink),
        };
        self.depth -= 1;
        self.in_generator = false;
        // Clean up the pull's scope (ch.31, M3-S29).
        while let Some(scope) = fr.scopes.pop() {
            let _ = self.run_cleanups(scope, out);
        }
        let mut cache = g.cache.lock().unwrap();
        cache.extend(self.pending_hands.drain(..));
        Ok(!matches!(run, Err(_)))
    }

    /// Execute the resumable body until its next Hand back or its end.
    fn gen_run_until_hand(
        &mut self,
        g: &sem::GeneratorHandle,
        fdef: &sem::FuncDef,
        out: &mut String,
    ) -> R<bool> {
        let mut st_store = g.resume.lock().unwrap();
        let mut st = st_store.clone();
        let mut fr = match st.frame_state.take() {
            Some(gs) => frame_from_gen(gs),
            None => {
                st.started = true;
                st.block = g.entry;
                st.step = 0;
                st.gcounters = vec![(0, 0); g.mir.counter_count];
                st.bounds_set = vec![false; g.mir.counter_count];
                let mut fr = Frame {
                    scopes: Vec::new(),
                    counters: Vec::new(),
                    last_result: None,
                    last_shown: String::new(),
                    where_item: None,
                    tasks: HashMap::new(),
                    timers: Vec::new(),
                    watchers: Vec::new(),
                };
                let mut sc = ScopeFrame::default();
                for (i, (n2, _)) in fdef.inputs.iter().enumerate() {
                    sc.vars.insert(
                        n2.clone(),
                        g.args
                            .get(i)
                            .map(|(_, v)| v.clone())
                            .unwrap_or(Value::Missing),
                    );
                    sc.order.push(n2.clone());
                }
                // captions frozen at creation (M3-D2)
                for (cap, v) in &g.caps {
                    sc.vars.insert(cap.clone(), v.clone());
                    sc.order.push(cap.clone());
                }
                fr.scopes.push(sc);
                fr
            }
        };
        self.depth += 1;
        if self.depth > 240 {
            self.depth -= 1;
            return Err(fatal("T0607", T0607_C, T0607_F));
        }
        let outcome = self.gen_exec(Some(g), &g.mir.clone(), &mut st, &mut fr, out);
        self.depth -= 1;
        match outcome {
            Ok(GHold::Hand(v)) => {
                // the state (pc + frozen frame) is already in st
                st.frame_state = Some(frame_to_gen(&fr));
                *st_store = st;
                let mut cache = g.cache.lock().unwrap();
                cache.push(v);
                Ok(true)
            }
            Ok(GHold::Done) => {
                // the body ended: clean up everything it still owns (ch.31)
                while let Some(scope) = fr.scopes.pop() {
                    let _ = self.run_cleanups(scope, out);
                }
                *st_store = sem::GenState::default();
                Ok(false)
            }
            // a generator body never parks: its Receive statements run
            // outside a live session (active_conn is None then)
            Ok(GHold::Parked) => Ok(false),
            Err(e) => Err(e),
        }
    }

    /// The resumable step loop of a generator body (ch.25, M3-D12): follow
    /// the body's block graph, suspend exactly at a Hand back, and run every
    /// non-control step through the original statement code via exec_stmt,
    /// so statement semantics stay identical to the plain interpreter.
    /// M4-S73/D13: the same loop drives a parked live session (g None);
    /// a Receive whose frame is not here yet parks it (GHold::Parked) and
    /// an observed close ends it (GHold::Done).
    fn gen_exec(
        &mut self,
        g: Option<&sem::GeneratorHandle>,
        mir: &mir::ProgramMir,
        st: &mut sem::GenState,
        frame: &mut Frame,
        out: &mut String,
    ) -> R<GHold> {
        loop {
            self.tick()?;
            let block = &mir.blocks[st.block];
            if st.step >= block.steps.len() {
                match &block.exit {
                    Some(t) => {
                        for _ in 0..t.pops {
                            frame.pop();
                        }
                        if t.push {
                            frame.push();
                        }
                        st.block = t.block;
                        st.step = 0;
                        continue;
                    }
                    None => return Ok(GHold::Done),
                }
            }
            let step = &block.steps[st.step];
            let orig = &block.origs[st.step];
            st.step += 1;
            match step {
                // ---- the suspension point (M3-D12) ----
                Step::HandBack { value } => {
                    let v = self.eval_expr(value, frame, out)?;
                    return Ok(GHold::Hand(v));
                }
                Step::Branch { cond, yes, no } => {
                    let take_yes = match cond {
                        Some(c) => as_truthy(&self.eval_expr(c, frame, out)?),
                        None => true,
                    };
                    match if take_yes { yes.clone() } else { no.clone() } {
                        Some(t) => {
                            for _ in 0..t.pops {
                                frame.pop();
                            }
                            if t.push {
                                frame.push();
                            }
                            st.block = t.block;
                            st.step = 0;
                        }
                        None => return Ok(GHold::Done),
                    }
                    continue;
                }
                Step::ForInit { counter, from, to } => {
                    // the bounds evaluate once, per body invocation; the
                    // visits after each Advance see the frozen values
                    let idx = *counter;
                    if !st.bounds_set.get(idx).copied().unwrap_or(true) {
                        let start = as_i64(&self.eval_expr(from, frame, out)?);
                        let lim = match to {
                            Some(te) => as_i64(&self.eval_expr(te, frame, out)?),
                            None => i64::MAX,
                        };
                        if idx < st.gcounters.len() {
                            st.gcounters[idx] = (start, lim);
                            st.bounds_set[idx] = true;
                        }
                    }
                    continue;
                }
                Step::ForCheck { counter, yes, no } => {
                    let ok = st.gcounters.get(*counter).map_or(false, |(c, l)| *c <= *l);
                    let t = if ok { yes.clone() } else { no.clone() };
                    for _ in 0..t.pops {
                        frame.pop();
                    }
                    if t.push {
                        frame.push();
                    }
                    st.block = t.block;
                    st.step = 0;
                    continue;
                }
                Step::Advance {
                    counter,
                    step: by,
                    target,
                } => {
                    if let Some(e) = st.gcounters.get_mut(*counter) {
                        e.0 = e.0.saturating_add(*by);
                    }
                    st.block = target.block;
                    st.step = 0;
                    // target: pops 0 and push false by construction
                    continue;
                }
                Step::DefineCounter { name, counter } => {
                    let v = st.gcounters.get(*counter).map_or(0, |(c, _)| *c);
                    frame.define(name, Value::Whole(v));
                    continue;
                }
                Step::Stop { pops, target } => {
                    for _ in 0..*pops {
                        frame.pop();
                    }
                    st.block = *target;
                    st.step = 0;
                    continue;
                }
                Step::Skip { pops, target } => {
                    for _ in 0..*pops {
                        frame.pop();
                    }
                    st.block = *target;
                    st.step = 0;
                    continue;
                }
                Step::GiveBack { .. } => {
                    // run the real give back; the body then ends
                    let flow = self.exec_stmt(orig, frame, out);
                    match flow {
                        Ok(_) => return Ok(GHold::Done),
                        Err(e) => return Err(e),
                    }
                }
                // ---- everything else runs the real statement code ----
                _ => {
                    let flow = self.exec_stmt(orig, frame, out);
                    // M4-S73/D13: a live Receive whose frame is not here
                    // yet parks the session right here - the pc sits back
                    // ON the Receive, which re-runs on resume. An observed
                    // close ends the session (S73).
                    if self.park_conn {
                        self.park_conn = false;
                        st.step = st.step.saturating_sub(1);
                        return Ok(GHold::Parked);
                    }
                    if self.end_session {
                        self.end_session = false;
                        return Ok(GHold::Done);
                    }
                    match flow {
                        Ok(Flow::Normal) | Ok(Flow::Skip) => {}
                        Ok(Flow::Stop) | Ok(Flow::Back(_, _)) => return Ok(GHold::Done),
                        Ok(Flow::Hand(v)) => {
                            // unreachable for resumable bodies (checked by
                            // gen_resume_safe); keep the value, never lose it
                            if let Some(g) = g {
                                g.cache.lock().unwrap().push(v);
                            }
                        }
                        Err(e) => return Err(e),
                    }
                }
            }
        }
    }

    // ------------------------------------------------------------ printing

    /// M4-9: the raw text of a Log line, built exactly as a Say builds
    /// its text: names in it are replaced (S87), a secret writes hidden
    /// (S89), a counter shows its value (S90), width/places mods apply.
    /// The text carries no line feed (Log writes exactly one, S87).
    fn log_text(
        &mut self,
        expr: &sem::Expr,
        mods: &SayMods,
        lines: &[String],
        frame: &mut Frame,
        out: &mut String,
    ) -> Result<String, TErr> {
        if !lines.is_empty() && matches!(&expr.e, E::Flat(v) if v.is_empty()) {
            let mut parts: Vec<&str> = Vec::new();
            for line in lines {
                parts.push(line.trim());
            }
            return Ok(parts.join(" "));
        }
        if let E::Flat(pieces) = &expr.e {
            let mut parts: Vec<String> = Vec::new();
            for p in pieces {
                let v = self.eval_expr(p, frame, out)?;
                parts.push(self.show_value(&v, mods));
            }
            let mut text = parts.join(" ");
            if let Some(w) = mods.width {
                if text.chars().count() < w {
                    text = format!("{}{}", " ".repeat(w - text.chars().count()), text);
                }
            }
            return Ok(text);
        }
        let v = self.eval_expr(expr, frame, out)?;
        Ok(self.show_value(&v, mods))
    }

    fn show_value(&self, v: &Value, mods: &SayMods) -> String {
        let mut s = match v {
            Value::Whole(x) => x.to_string(),
            Value::Big(limbs) => big_to_string(limbs),
            Value::Dec(x) => format_decimal(*x, mods.places.unwrap_or(2)),
            Value::Boolean(b) => {
                if *b {
                    "yes".to_string()
                } else {
                    "no".to_string()
                }
            }
            Value::Text(t) => t.clone(),
            Value::Missing => "missing".to_string(),
            // M4-S73: a connection prints as the kind's word.
            Value::Conn(_) => "connection".to_string(),
            Value::List(items) => {
                let empty = SayMods::default();
                let parts: Vec<String> = items.iter().map(|t| self.show_value(t, &empty)).collect();
                join_and(&parts)
            }
            Value::Pair(a, b) => {
                let empty = SayMods::default();
                format!(
                    "{} and {}",
                    self.show_value(a, &empty),
                    self.show_value(b, &empty)
                )
            }
            Value::Map(entries) => {
                let empty = SayMods::default();
                let parts: Vec<String> = entries
                    .iter()
                    .map(|(k, v)| {
                        format!(
                            "{} => {}",
                            self.show_value(k, &empty),
                            self.show_value(v, &empty)
                        )
                    })
                    .collect();
                parts.join(", ")
            }
            Value::Set(items) => {
                let empty = SayMods::default();
                let parts: Vec<String> = items.iter().map(|t| self.show_value(t, &empty)).collect();
                join_and(&parts)
            }
            Value::Queue(items) => {
                let empty = SayMods::default();
                let parts: Vec<String> = items.iter().map(|t| self.show_value(t, &empty)).collect();
                join_and(&parts)
            }
            Value::Array(slots) => {
                let empty = SayMods::default();
                let parts: Vec<String> = slots
                    .iter()
                    .map(|t| match t {
                        Some(v) => self.show_value(v, &empty),
                        None => "?".to_string(),
                    })
                    .collect();
                parts.join(", ")
            }
            Value::Record(_, parts) => {
                let empty = SayMods::default();
                let parts_s: Vec<String> = parts
                    .iter()
                    .map(|(n, v)| format!("{} {}", n, self.show_value(v, &empty)))
                    .collect();
                parts_s.join(", ")
            }
            Value::Share(v) => self.show_value(v, mods),
            Value::WeakShare(v) => self.show_value(v, mods),
            // M4 (Appendix K): a channel prints the items it still holds;
            // a guarded value prints its inner value; an atomic or a
            // counter prints its current number (M4-S20).
            Value::Channel(state) => {
                let empty = SayMods::default();
                let st = state.borrow();
                let parts: Vec<String> = st
                    .queue
                    .iter()
                    .map(|t| self.show_value(t, &empty))
                    .collect();
                join_and(&parts)
            }
            Value::Guarded(v) => self.show_value(v, mods),
            Value::Atomic(n) => n.to_string(),
            Value::Counter(n) => n.to_string(),
            Value::Enum { variant, .. } => variant.clone(),
            Value::Maybe(maybe) => match maybe {
                Some(v) => self.show_value(v, mods),
                None => "missing".to_string(),
            },
            Value::Closure { func, .. } => format!("[function {func}]"),
            Value::Dyn { value, .. } => self.show_value(value, mods),
            Value::Generator(g) => format!("[generator {}]", g.func),
            Value::FunctionRef(name) => format!("[function {name}]"),
            // ---- M4-7 (Appendix K 7.7) ----
            // M4-S53: a date prints 2026-10-31; a moment prints
            // 2026-10-31T14:30:00+06:00; a duration prints the largest
            // units that fit joined by and (0 seconds when empty).
            Value::Date(y, m, d) => crate::time4::fmt_date(*y, *m, *d),
            Value::Moment { nanos, zone } => crate::time4::fmt_moment(*nanos, zone),
            Value::Duration(n) => crate::time4::fmt_duration(*n),
            // M4-S56: a secret prints as hidden.
            Value::Secret(_) => "hidden".to_string(),
        };
        if let Some(w) = mods.width {
            if s.len() < w {
                s = format!("{}{}", " ".repeat(w - s.len()), s);
            }
        }
        s
    }
}

fn bin_op(op: Op, a: &Value, b: &Value) -> R<Value> {
    if let (Value::Whole(x), Value::Whole(y)) = (a, b) {
        return match op {
            Op::Plus => x
                .checked_add(*y)
                .map(Value::Whole)
                .ok_or_else(|| fatal("T0603", T0603_C, T0603_F)),
            Op::Minus => x
                .checked_sub(*y)
                .map(Value::Whole)
                .ok_or_else(|| fatal("T0603", T0603_C, T0603_F)),
            Op::Time => x
                .checked_mul(*y)
                .map(Value::Whole)
                .ok_or_else(|| fatal("T0603", T0603_C, T0603_F)),
            Op::CheckedPlus => x
                .checked_add(*y)
                .map(Value::Whole)
                .ok_or_else(|| TErr::Signal),
            Op::CheckedMinus => x
                .checked_sub(*y)
                .map(Value::Whole)
                .ok_or_else(|| TErr::Signal),
            Op::CheckedTimes => x
                .checked_mul(*y)
                .map(Value::Whole)
                .ok_or_else(|| TErr::Signal),
            Op::WrappingPlus => Ok(Value::Whole(x.wrapping_add(*y))),
            Op::WrappingMinus => Ok(Value::Whole(x.wrapping_sub(*y))),
            Op::WrappingTimes => Ok(Value::Whole(x.wrapping_mul(*y))),
            Op::SaturatingPlus => Ok(Value::Whole(x.saturating_add(*y))),
            Op::SaturatingMinus => Ok(Value::Whole(x.saturating_sub(*y))),
            Op::SaturatingTimes => Ok(Value::Whole(x.saturating_mul(*y))),
            Op::DividedBy => Ok(Value::Dec(*x as f64 / *y as f64)),
            _ => Ok(Value::Whole(*x)),
        };
    }
    if let (Value::Big(_), _) | (_, Value::Big(_)) = (a, b) {
        return big_op(op, a, b);
    }
    if let (Value::Dec(x), Value::Dec(y)) = (a, b) {
        return Ok(Value::Dec(match op {
            Op::Plus => x + y,
            Op::Minus => x - y,
            Op::Time => x * y,
            Op::DividedBy => {
                if *y == 0.0 {
                    f64::INFINITY
                } else {
                    x / y
                }
            }
            _ => 0.0,
        }));
    }
    // a mixed kind at run time (values came from unknown-kind sources)
    if is_num(a) && is_num(b) {
        let (x, y) = (as_f64(a), as_f64(b));
        return Ok(Value::Dec(match op {
            Op::Plus => x + y,
            Op::Minus => x - y,
            Op::Time => x * y,
            Op::DividedBy => {
                if y == 0.0 {
                    f64::INFINITY
                } else {
                    x / y
                }
            }
            _ => 0.0,
        }));
    }
    Ok(Value::Missing)
}

fn big_op(op: Op, a: &Value, b: &Value) -> R<Value> {
    let (big, other): (Vec<u32>, i64) = match a {
        Value::Big(n) => (n.clone(), as_i64(b)),
        _ => match b {
            Value::Big(n) => (n.clone(), as_i64(a)),
            _ => return Ok(Value::Missing),
        },
    };
    let o = match big_from_i64(other) {
        Some(o) => o,
        None => return Err(not_allowed()), // M1b big values are never negative
    };
    match op {
        Op::Plus => Ok(Value::Big(big_add(&big, &o))),
        Op::Minus => match big_sub(&big, &o) {
            Some(r) => Ok(Value::Big(r)),
            None => Err(TErr::Fatal(
                "Error: Big numbers do not go below zero until milestone M2.".to_string(),
            )),
        },
        Op::Time => Ok(Value::Big(big_mul(&big, &o))),
        _ => Err(TErr::Fatal(
            "Error: Big numbers take that operation from milestone M2.".to_string(),
        )),
    }
}

/// Decimals print with `places` decimals, rounded half away from zero, never
/// with an exponent (Ch.10). Minus zero prints as 0.00.
pub fn format_decimal(x: f64, places: usize) -> String {
    if !x.is_finite() {
        if x.is_nan() {
            return "missing".to_string();
        }
        return if x > 0.0 {
            "infinity".to_string()
        } else {
            "minus infinity".to_string()
        };
    }
    let scale = 10f64.powi(places as i32);
    let mut n = (x * scale).round(); // half away from zero
    if n == 0.0 {
        n = 0.0; // minus zero keeps the digits, drops the sign
    }
    let negative = n < 0.0;
    let n_abs = n.abs() as u128;
    let iv = n_abs / scale as u128;
    let frac = n_abs % scale as u128;
    let mut frac_s = frac.to_string();
    while frac_s.len() < places {
        frac_s.insert(0, '0');
    }
    let mut s = if places == 0 {
        iv.to_string()
    } else {
        format!("{iv}.{frac_s}")
    };
    if negative && (iv != 0 || frac != 0) {
        s = format!("-{s}");
    }
    s
}

fn parse_number(t: &str) -> Option<Value> {
    let t = t.trim();
    if let Ok(w) = t.parse::<i64>() {
        return Some(Value::Whole(w));
    }
    if let Ok(d) = t.parse::<f64>() {
        return Some(Value::Dec(d));
    }
    None
}

fn as_i64(v: &Value) -> i64 {
    match v {
        Value::Whole(x) => *x,
        Value::Dec(x) => x.round() as i64,
        Value::Big(b) => big_to_f64(b).max(i64::MIN as f64).min(i64::MAX as f64) as i64,
        Value::Boolean(b) => *b as i64,
        _ => 0,
    }
}

fn as_f64(v: &Value) -> f64 {
    match v {
        Value::Whole(x) => *x as f64,
        Value::Dec(x) => *x,
        Value::Big(b) => big_to_f64(b),
        Value::Boolean(b) => *b as i64 as f64,
        _ => 0.0,
    }
}

fn is_num(v: &Value) -> bool {
    matches!(v, Value::Whole(_) | Value::Dec(_) | Value::Big(_))
}

fn as_truthy(v: &Value) -> bool {
    matches!(v, Value::Boolean(true))
}

/// Ch.16: the it-too-far message names what the sentence before printed.
fn it_too_far(shown: &str) -> String {
    if shown.is_empty() {
        "it means the result of the sentence just before. Give the result a name.".to_string()
    } else {
        format!(
            "it means the result of the sentence just before, and the sentence before printed {shown}. Give the result a name."
        )
    }
}

/// Say list. prints "a, b and c" (Ch.16).
fn join_and(parts: &[String]) -> String {
    match parts.len() {
        0 => String::new(),
        1 => parts[0].clone(),
        n => format!("{} and {}", parts[..n - 1].join(", "), parts[n - 1]),
    }
}

/// Combine <list> with <word>. folds the items with the word op (Ch.16).
fn combine_step(a: Value, b: Value, word: &str) -> R<Value> {
    let op = match word {
        "plus" => Op::Plus,
        "minus" => Op::Minus,
        "times" => Op::Time,
        _ => {
            return Err(fatal(
                "T0509",
                &format!("Combine with {word} arrives in milestone M2."),
                "Work with plus until M2.",
            ));
        }
    };
    bin_op(op, &a, &b)
}

fn as_text(v: &Value) -> String {
    match v {
        Value::Text(t) => t.clone(),
        Value::Boolean(true) => "yes".to_string(),
        Value::Boolean(false) => "no".to_string(),
        Value::Missing => String::new(),
        _ => String::new(),
    }
}

/// Read a part of a record value (ch.20). A part of a missing maybe stays
/// missing; any other kind is not allowed.
fn part_of_value(v: &Value, part: &str, type_name: &str) -> R<Value> {
    match v {
        Value::Record(_, rparts) => rparts
            .iter()
            .find(|(n, _)| n == part)
            .map(|(_, x)| x.clone())
            .ok_or_else(|| {
                fatal(
                    "T0314",
                    &format!("A {type_name} has no part called {part}."),
                    &format!("Use a part the {type_name} has."),
                )
            }),
        Value::Maybe(m) => match m {
            Some(inner) => part_of_value(inner, part, type_name),
            None => Ok(Value::Missing),
        },
        _ => Err(not_allowed()),
    }
}

/// Write a part of a record value in place, following the part path
/// (Set street of home of maya to Oak., ch.20).
fn set_part_into(cur: &mut Value, parts: &[String], v: &Value) -> R<()> {
    let Some(part) = parts.first() else {
        return Ok(());
    };
    match cur {
        Value::Record(_, rparts) => {
            if let Some(slot) = rparts.iter_mut().find(|(n, _)| n == part) {
                if parts.len() == 1 {
                    slot.1 = v.clone();
                    Ok(())
                } else {
                    set_part_into(&mut slot.1, &parts[1..], v)
                }
            } else {
                Err(fatal(
                    "T0314",
                    &format!("A record has no part called {part}."),
                    "Use a part the record has.",
                ))
            }
        }
        _ => Err(not_allowed()),
    }
}

fn cmp_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Text(x), Value::Text(y)) => x == y,
        (Value::Boolean(x), Value::Boolean(y)) => x == y,
        (Value::Whole(x), Value::Whole(y)) => x == y,
        (Value::Big(x), Value::Big(y)) => big_cmp(x, y) == std::cmp::Ordering::Equal,
        (Value::Big(x), Value::Whole(y)) => match big_from_i64(*y) {
            Some(w) => big_cmp(x, &w) == std::cmp::Ordering::Equal,
            None => false,
        },
        (Value::Whole(x), Value::Big(y)) => match big_from_i64(*x) {
            Some(w) => big_cmp(&w, y) == std::cmp::Ordering::Equal,
            None => false,
        },
        (Value::Missing, Value::Missing) => true,
        (Value::List(x), Value::List(y)) => {
            x.len() == y.len() && x.iter().zip(y).all(|(a, b)| cmp_eq(a, b))
        }
        (Value::Pair(x1, x2), Value::Pair(y1, y2)) => cmp_eq(x1, y1) && cmp_eq(x2, y2),
        (Value::Record(_, x), Value::Record(_, y)) => {
            // parts compare by name, in any order (ch.20)
            x.len() == y.len()
                && x.iter().all(|(n, xv)| {
                    y.iter()
                        .find(|(yn, _)| yn == n)
                        .map_or(false, |(_, yv)| cmp_eq(xv, yv))
                })
        }
        (
            Value::Enum {
                variant: v1,
                parts: p1,
            },
            Value::Enum {
                variant: v2,
                parts: p2,
            },
        ) => v1 == v2 && p1.len() == p2.len() && p1.iter().zip(p2).all(|(a, b)| cmp_eq(a, b)),
        (Value::Share(a), Value::Share(b)) => cmp_eq(a, b),
        // ---- M4-7 (Appendix K 7.7) ----
        (Value::Date(y1, m1, d1), Value::Date(y2, m2, d2)) => y1 == y2 && m1 == m2 && d1 == d2,
        // a moment equals another by the instant alone
        (Value::Moment { nanos: n1, .. }, Value::Moment { nanos: n2, .. }) => n1 == n2,
        (Value::Duration(x), Value::Duration(y)) => x == y,
        _ => false,
    }
}

/// A missing value: missing itself, or a maybe that is absent (ch.18).
fn is_missing_like(v: &Value) -> bool {
    match v {
        Value::Missing => true,
        Value::Maybe(m) => match m {
            None => true,
            Some(x) => matches!(**x, Value::Missing),
        },
        _ => false,
    }
}

/// How many items a collection holds; text counts letters (graphemes later, ch.14).
fn count_items(v: &Value) -> i64 {
    match v {
        Value::List(items) => items.len() as i64,
        Value::Map(m) => m.len() as i64,
        Value::Set(s) => s.len() as i64,
        Value::Queue(q) => q.len() as i64,
        Value::Record(_, r) => r.len() as i64,
        // an array has a fixed size: how many in counts every slot, set or
        // not (Appendix I M2-T35: an array of 8 numbers prints 8)
        Value::Array(slots) => slots.len() as i64,
        Value::Share(slots) => count_items(slots),
        Value::Enum { .. } => 1,
        Value::Pair(_, _) => 2,
        Value::Maybe(None) => 0,
        Value::Maybe(Some(x)) => count_items(x),
        // a text counts what a reader sees as one letter (ch.14: UAX 29)
        other => graphemes_of(&as_text(other)).count() as i64,
    }
}

fn numeric(v: &Value) -> Option<f64> {
    match v {
        Value::Whole(x) => Some(*x as f64),
        Value::Dec(x) => Some(*x),
        Value::Big(b) => Some(big_to_f64(b)),
        _ => None,
    }
}

fn cmp_ord(a: &Value, b: &Value) -> R<std::cmp::Ordering> {
    // M4-7 (S56): a secret cannot be compared (ordered questions, the
    // bigger/smaller reads, sorting and Between all come through here).
    if matches!(a, Value::Secret(_)) || matches!(b, Value::Secret(_)) {
        return Err(TErr::Signal);
    }
    // Text compares by Unicode code point (ch.22), so words order on their
    // own: bigger of apple and pear is pear.
    if let (Value::Text(x), Value::Text(y)) = (a, b) {
        return Ok(x.as_bytes().cmp(y.as_bytes()));
    }
    // M4-7: dates order by the calendar day; moments by the instant
    // alone; durations by length.
    if let (Value::Date(y1, m1, d1), Value::Date(y2, m2, d2)) = (a, b) {
        let n1 = crate::time4::days_from_civil(*y1, *m1, *d1);
        let n2 = crate::time4::days_from_civil(*y2, *m2, *d2);
        return Ok(n1.cmp(&n2));
    }
    if let (Value::Moment { nanos: n1, .. }, Value::Moment { nanos: n2, .. }) = (a, b) {
        return Ok(n1.cmp(n2));
    }
    if let (Value::Duration(x), Value::Duration(y)) = (a, b) {
        return Ok(x.cmp(y));
    }
    let (Some(x), Some(y)) = (numeric(a), numeric(b)) else {
        return Err(not_allowed());
    };
    Ok(x.partial_cmp(&y).unwrap_or(std::cmp::Ordering::Equal))
}

fn cmp_close(a: &Value, b: &Value) -> bool {
    let (Some(x), Some(y)) = (numeric(a), numeric(b)) else {
        return false;
    };
    let limit = (x.abs().max(y.abs()) / 1_000_000_000.0).max(0.000000000001);
    (x - y).abs() <= limit
}

// ------------------------------------------------------------ big numbers
// Vec<u32>, little-endian limbs, base 1e9 (base-1e9 limbs make printing easy;
// each limb holds 9 decimal digits).

fn big_from_i64(x: i64) -> Option<Vec<u32>> {
    if x < 0 {
        return None; // big values in M1b are never negative
    }
    let mut n = x as u64;
    let mut limbs: Vec<u32> = Vec::new();
    if n == 0 {
        limbs.push(0);
        return Some(limbs);
    }
    while n > 0 {
        limbs.push((n % 1_000_000_000) as u32);
        n /= 1_000_000_000;
    }
    Some(limbs)
}

fn big_add(a: &[u32], b: &[u32]) -> Vec<u32> {
    let len = a.len().max(b.len());
    let mut out: Vec<u32> = Vec::with_capacity(len + 1);
    let mut carry: u64 = 0;
    for i in 0..len {
        let x = *a.get(i).unwrap_or(&0) as u64;
        let y = *b.get(i).unwrap_or(&0) as u64;
        let s = x + y + carry;
        out.push((s % 1_000_000_000) as u32);
        carry = s / 1_000_000_000;
    }
    if carry > 0 {
        out.push(carry as u32);
    }
    out
}

/// a - b for a >= b; None when it would go below zero.
fn big_sub(a: &[u32], b: &[u32]) -> Option<Vec<u32>> {
    match big_cmp(a, b) {
        std::cmp::Ordering::Less => return None,
        _ => {}
    }
    let mut out: Vec<u32> = Vec::with_capacity(a.len());
    let mut borrow: i64 = 0;
    for i in 0..a.len() {
        let x = *a.get(i).unwrap_or(&0) as i64 - borrow;
        let y = *b.get(i).unwrap_or(&0) as i64;
        let (x, y) = if x < y {
            (x + 1_000_000_000, y)
        } else {
            (x, y)
        };
        out.push((x - y) as u32);
        borrow = if x >= 1_000_000_000 { 1 } else { 0 };
    }
    while out.len() > 1 && *out.last().unwrap() == 0 {
        out.pop();
    }
    Some(out)
}

fn big_mul(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = vec![0u32; a.len() + b.len()];
    for i in 0..a.len() {
        let mut carry: u64 = 0;
        for j in 0..b.len() {
            let cur = out[i + j] as u64;
            let prod = (a[i] as u64) * (b[j] as u64) + cur + carry;
            out[i + j] = (prod % 1_000_000_000) as u32;
            carry = prod / 1_000_000_000;
        }
        let mut k = i + b.len();
        let mut carry = carry;
        while carry > 0 {
            let cur = *out.get(k).unwrap_or(&0) as u64;
            let s = cur + carry;
            if k < out.len() {
                out[k] = (s % 1_000_000_000) as u32;
            } else {
                out.push((s % 1_000_000_000) as u32);
            }
            carry = s / 1_000_000_000;
            k += 1;
        }
    }
    while out.len() > 1 && *out.last().unwrap() == 0 {
        out.pop();
    }
    out
}

fn big_factorial(n: i64) -> Vec<u32> {
    let mut limbs: Vec<u32> = vec![1];
    for k in 2..=n {
        let mut carry: u64 = 0;
        for limb in limbs.iter_mut() {
            let v = (*limb as u64) * (k as u64) + carry;
            *limb = (v % 1_000_000_000) as u32;
            carry = v / 1_000_000_000;
        }
        while carry > 0 {
            limbs.push((carry % 1_000_000_000) as u32);
            carry /= 1_000_000_000;
        }
    }
    limbs
}

fn big_cmp(a: &[u32], b: &[u32]) -> std::cmp::Ordering {
    let mut la = a.len();
    let mut lb = b.len();
    while la > 1 && a[la - 1] == 0 {
        la -= 1;
    }
    while lb > 1 && b[lb - 1] == 0 {
        lb -= 1;
    }
    let _ = &mut (la, lb);
    if la != lb {
        return la.cmp(&lb);
    }
    for i in (0..la).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    std::cmp::Ordering::Equal
}

fn big_to_f64(b: &[u32]) -> f64 {
    let mut v = 0.0f64;
    for (i, limb) in b.iter().enumerate().rev() {
        v += *limb as f64 * 10f64.powi((i as i32) * 9);
    }
    v
}

fn big_to_string(b: &[u32]) -> String {
    match b.split_last() {
        Some((last, rest)) => {
            let mut s = last.to_string();
            for limb in rest.iter().rev() {
                s.push_str(&format!("{limb:09}"));
            }
            s
        }
        None => "0".to_string(),
    }
}

/// item N of list: 1-based, panics (T0601) out of range.
fn item_n_of(items: &[Value], n: i64) -> R<Value> {
    if n < 1 || (n as usize) > items.len() {
        Err(fatal(
            "T0601",
            "Item out of range.",
            "Ask for an item from 1 to N, or use safe item.",
        ))
    } else {
        Ok(items[(n - 1) as usize].clone())
    }
}

/// 1-based position of `needle` text inside `haystack` text, counted in
/// grapheme clusters as a reader sees them (ch.14).
fn as_text_pos(haystack: &str, needle: &Value) -> Option<i64> {
    let needle = match needle {
        Value::Text(t) => t.clone(),
        _ => return None,
    };
    if needle.is_empty() {
        return None;
    }
    haystack
        .find(&needle)
        .map(|p| graphemes_of(&haystack[..p]).count() as i64 + 1)
}

// ------------------------------------------------------------ patterns (ch.14)

/// Does one pattern part match here, without backtracking? Returns the byte
/// position after the part. Greedy: one-or-more takes the longest run.
fn pat_at(parts: &[Pat], t: &str, mut pos: usize) -> Option<usize> {
    for part in parts {
        pos = pat_part_at(part, t, pos)?;
    }
    Some(pos)
}

fn pat_part_at(pat: &Pat, t: &str, pos: usize) -> Option<usize> {
    match pat {
        Pat::Word(w) => {
            if t[pos..].starts_with(w.as_str()) {
                Some(pos + w.len())
            } else {
                None
            }
        }
        Pat::Digits => one_char(t, pos, |c| c.is_numeric()),
        Pat::Letters => one_char(t, pos, |c| c.is_alphabetic()),
        Pat::Spaces => one_char(t, pos, |c| c.is_whitespace()),
        Pat::Anything => t[pos..].chars().next().map(|c| pos + c.len_utf8()),
        Pat::OneOrMore(inner) => {
            let mut p = pos;
            let mut last = None;
            while let Some(next) = pat_part_at(inner, t, p) {
                last = Some(next);
                p = next;
            }
            last
        }
        Pat::Optional(inner) => match pat_part_at(inner, t, pos) {
            Some(next) => Some(next),
            None => Some(pos),
        },
        Pat::StartsWith(inner) => {
            if pos == 0 {
                pat_part_at(inner, t, pos)
            } else {
                None
            }
        }
        Pat::EndsWith(inner) => pat_part_at(inner, t, pos).filter(|p| *p == t.len()),
    }
}

fn one_char(t: &str, pos: usize, ok: fn(char) -> bool) -> Option<usize> {
    match t[pos..].chars().next() {
        Some(c) if ok(c) => Some(pos + c.len_utf8()),
        _ => None,
    }
}

/// Leftmost, longest match of a pattern in a text: byte (start, end).
fn pat_find(parts: &[Pat], t: &str) -> Option<(usize, usize)> {
    let mut start = 0;
    while start <= t.len() {
        if let Some(end) = pat_at(parts, t, start) {
            return Some((start, end));
        }
        let Some(c) = t[start..].chars().next() else {
            break;
        };
        start += c.len_utf8();
    }
    None
}

/// The leftmost, longest match of every non-overlapping hit: byte ranges.
fn pat_all(parts: &[Pat], t: &str) -> Vec<(usize, usize)> {
    let mut hits = Vec::new();
    let mut pos = 0;
    while pos <= t.len() {
        if let Some(end) = pat_at(parts, t, pos) {
            hits.push((pos, end));
            if end > pos {
                pos = end;
            } else {
                // a zero-width hit: step one character so the scan moves on
                let Some(c) = t[pos..].chars().next() else {
                    break;
                };
                pos += c.len_utf8();
            }
        } else {
            let Some(c) = t[pos..].chars().next() else {
                break;
            };
            pos += c.len_utf8();
        }
    }
    hits
}

/// A generated input for a property test (ch.38): seed 42, 100 inputs.
/// Only the basic kinds are generated; anything else yields Missing.
fn gen_value(kind_words: &str, next: &mut impl FnMut() -> u64) -> Value {
    let small = (next() % 21) as i64 - 10; // -10..=10 keeps arithmetic in range
    match kind_words {
        "number" | "whole" => Value::Whole(small),
        "decimal" => Value::Dec(small as f64 + (next() % 100) as f64 / 100.0),
        "text" => {
            let letters = ['a', 'b', 'c', 'd', 'e'];
            let n = (next() % 5) as usize;
            let s: String = (0..n).map(|_| letters[(next() % 5) as usize]).collect();
            Value::Text(s)
        }
        "truth" => Value::Boolean(next() % 2 == 0),
        "letter" => Value::Text(
            "abcde"
                .chars()
                .nth((next() % 5) as usize)
                .unwrap()
                .to_string(),
        ),
        "list of numbers" => {
            let n = (next() % 5) as usize;
            Value::List(
                (0..n)
                    .map(|_| Value::Whole((next() % 21) as i64 - 10))
                    .collect(),
            )
        }
        "list of texts" => {
            let n = (next() % 4) as usize;
            Value::List((0..n).map(|_| gen_value("text", next)).collect())
        }
        other => {
            if let Some(rest) = other.strip_prefix("list of ") {
                let n = (next() % 4) as usize;
                Value::List((0..n).map(|_| gen_value(rest, next)).collect())
            } else if other.starts_with("maybe ") {
                if next() % 3 == 0 {
                    Value::Maybe(None)
                } else {
                    Value::Maybe(Some(Box::new(gen_value(&other[6..], next))))
                }
            } else {
                Value::Missing
            }
        }
    }
}

/// The primes up to n, in order (M3-D12): the built-in sequence
/// `primes to N` (Ch.25).
fn primes_to(n: i64) -> Vec<Value> {
    let mut out = Vec::new();
    for candidate in 2..=n {
        let mut is_prime = true;
        let mut d = 2;
        while d * d <= candidate {
            if candidate % d == 0 {
                is_prime = false;
                break;
            }
            d += 1;
        }
        if is_prime {
            out.push(Value::Whole(candidate));
        }
    }
    out
}

/// The kind of a value, in the words of the grammar (M3-S18 error text).
fn kind_word_of(v: &Value) -> String {
    match v {
        Value::Whole(_) => "whole number".to_string(),
        Value::Big(_) => "big number".to_string(),
        Value::Dec(_) => "decimal".to_string(),
        Value::Boolean(_) => "truth".to_string(),
        Value::Text(_) => "text".to_string(),
        Value::List(_) => "list".to_string(),
        Value::Pair(_, _) => "pair".to_string(),
        Value::Map(_) => "map".to_string(),
        Value::Set(_) => "set".to_string(),
        Value::Queue(_) => "queue".to_string(),
        Value::Array(_) => "array".to_string(),
        Value::Record(t, _) => t.clone(),
        Value::Enum { variant, .. } => variant.clone(),
        Value::Share(_) => "shared".to_string(),
        Value::WeakShare(_) => "link".to_string(),
        Value::Maybe(_) => "maybe".to_string(),
        Value::Missing => "missing".to_string(),
        Value::Closure { func, .. } => format!("function {func}"),
        Value::Dyn { type_name, .. } => type_name.clone(),
        Value::Generator(g) => format!("generator {}", g.func),
        Value::FunctionRef(name) => format!("function {name}"),
        // M4 (Appendix K): the words of the new value kinds
        Value::Channel(_) => "channel".to_string(),
        Value::Guarded(_) => "guarded".to_string(),
        Value::Atomic(_) => "atomic number".to_string(),
        Value::Counter(_) => "counter".to_string(),
        // M4-7 (Appendix K 7.7): the words of the new value kinds
        Value::Date(_, _, _) => "date".to_string(),
        Value::Moment { .. } => "moment".to_string(),
        Value::Duration(_) => "duration".to_string(),
        Value::Secret(_) => "secret".to_string(),
        // M4-S73: one live connection
        Value::Conn(_) => "connection".to_string(),
    }
}

// ---- M4 (Appendix K 7.5, M4-S41) zip, zip-gzip, folder-copy helpers ----

/// CRC-32 (IEEE), table-based, in-house so the archive format does not
/// need an extra dependency (deflate comes from flate2).
fn crc32(data: &[u8]) -> u32 {
    let mut table = [0u32; 256];
    for i in 0..256u32 {
        let mut c = i;
        for _ in 0..8 {
            c = if c & 1 != 0 {
                0xedb8_8320 ^ (c >> 1)
            } else {
                c >> 1
            };
        }
        table[i as usize] = c;
    }
    let mut crc = 0xffff_ffffu32;
    for b in data {
        crc = table[((crc ^ (*b as u32)) & 0xff) as usize] ^ (crc >> 8);
    }
    !crc
}

/// The fixed DOS stamp of the first day of 1980 (M4-S41: archives are
/// reproducible): the date field 0x0021 (month 1, day 1) and time 0.
const DOS_FILE_DATE: u16 = 0x0021;

fn push16(out: &mut Vec<u8>, v: u16) {
    out.extend_from_slice(&v.to_le_bytes());
}
fn push32(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_le_bytes());
}

/// The files of a folder, recursively, with sorted relative paths and
/// the zip spec's forward slashes.
fn zip_entries(
    dir: &std::path::Path,
    base: &str,
    out: &mut Vec<(String, std::path::PathBuf)>,
) -> std::io::Result<()> {
    let rd = std::fs::read_dir(dir)?;
    let mut items: Vec<std::path::PathBuf> = rd.filter_map(|e| e.ok().map(|e| e.path())).collect();
    items.sort();
    for p in items {
        let rel = if base.is_empty() {
            p.file_name().unwrap().to_string_lossy().to_string()
        } else {
            format!("{base}/{}", p.file_name().unwrap().to_string_lossy())
        };
        if p.is_dir() {
            zip_entries(&p, &rel, out)?;
        } else if p.is_file() {
            out.push((rel, p));
        }
    }
    Ok(())
}

/// M4-S41: write a reproducible deflate ZIP archive of FOLDER to FILE.
fn write_zip(src: &std::path::Path, dst: &std::path::Path) -> std::io::Result<()> {
    let mut files: Vec<(String, std::path::PathBuf)> = Vec::new();
    zip_entries(src, "", &mut files)?;
    files.sort_by(|a, b| a.0.cmp(&b.0));

    let mut body: Vec<u8> = Vec::new(); // local file headers + payloads
    let mut central: Vec<u8> = Vec::new(); // the central directory
    for (rel, path) in &files {
        let raw = std::fs::read(path)?;
        let mut enc =
            flate2::write::DeflateEncoder::new(Vec::new(), flate2::Compression::default());
        enc.write_all(&raw)?;
        let deflated = enc.finish()?;
        let crc = crc32(&raw);
        let offset = body.len() as u32;
        let name = rel.as_bytes().to_vec();

        // local file header
        push32(&mut body, 0x0403_4b50);
        push16(&mut body, 20); // version needed
        push16(&mut body, 0); // flags
        push16(&mut body, 8); // method: deflate
        push16(&mut body, 0); // time 00:00:00
        push16(&mut body, DOS_FILE_DATE);
        push32(&mut body, crc);
        push32(&mut body, deflated.len() as u32);
        push32(&mut body, raw.len() as u32);
        push16(&mut body, name.len() as u16);
        push16(&mut body, 0); // extra length
        body.extend_from_slice(&name);
        body.extend_from_slice(&deflated);

        // central directory entry
        push32(&mut central, 0x0201_4b50);
        push16(&mut central, 20); // version made by
        push16(&mut central, 20); // version needed
        push16(&mut central, 0); // flags
        push16(&mut central, 8); // method
        push16(&mut central, 0); // time
        push16(&mut central, DOS_FILE_DATE);
        push32(&mut central, crc);
        push32(&mut central, deflated.len() as u32);
        push32(&mut central, raw.len() as u32);
        push16(&mut central, name.len() as u16);
        push16(&mut central, 0); // extra
        push16(&mut central, 0); // comment
        push16(&mut central, 0); // disk number
        push16(&mut central, 0); // internal attrs
        push32(&mut central, 0); // external attrs
        push32(&mut central, offset);
        central.extend_from_slice(&name);
    }
    let mut out = body;
    let central_offset = out.len() as u32;
    out.extend_from_slice(&central);
    // end of central directory
    push32(&mut out, 0x0605_4b50);
    push16(&mut out, 0); // this disk
    push16(&mut out, 0); // disk of the central dir
    push16(&mut out, files.len() as u16);
    push16(&mut out, files.len() as u16);
    push32(&mut out, central.len() as u32);
    push32(&mut out, central_offset);
    push16(&mut out, 0); // comment length
    std::fs::write(dst, out)
}

/// Read a zip archive's central directory and inflate its files into
/// DST (the target folder, made when needed).
fn unzip_archive(src: &std::path::Path, dst: &std::path::Path) -> std::io::Result<()> {
    std::fs::create_dir_all(dst)?;
    let data = std::fs::read(src)?;
    // the end-of-central-directory record is found from the tail
    let mut eocd = None;
    if data.len() >= 22 {
        let lo = data.len().saturating_sub(22 + 0xffff);
        let mut i = data.len() - 22;
        loop {
            if data[i..].starts_with(&0x0605_4b50u32.to_le_bytes()) {
                eocd = Some(i);
                break;
            }
            if i == lo {
                break;
            }
            i -= 1;
        }
    }
    let Some(eocd) = eocd else {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "not a zip archive",
        ));
    };
    let count = u16::from_le_bytes([data[eocd + 10], data[eocd + 11]]) as usize;
    let mut pos = u32::from_le_bytes([
        data[eocd + 16],
        data[eocd + 17],
        data[eocd + 18],
        data[eocd + 19],
    ]) as usize;
    for _ in 0..count {
        // one central directory entry
        if !data[pos..].starts_with(&0x0201_4b50u32.to_le_bytes()) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "bad central directory",
            ));
        }
        let method = u16::from_le_bytes([data[pos + 10], data[pos + 11]]);
        let csize = u32::from_le_bytes([
            data[pos + 20],
            data[pos + 21],
            data[pos + 22],
            data[pos + 23],
        ]) as usize;
        let name_len = u16::from_le_bytes([data[pos + 28], data[pos + 29]]) as usize;
        let extra_len = u16::from_le_bytes([data[pos + 30], data[pos + 31]]) as usize;
        let comment_len = u16::from_le_bytes([data[pos + 32], data[pos + 33]]) as usize;
        let offset = u32::from_le_bytes([
            data[pos + 42],
            data[pos + 43],
            data[pos + 44],
            data[pos + 45],
        ]) as usize;
        let name = String::from_utf8_lossy(&data[pos + 46..pos + 46 + name_len]).to_string();
        pos += 46 + name_len + extra_len + comment_len;

        // the local file header at OFFSET (its fields may differ)
        if !data[offset..].starts_with(&0x0403_4b50u32.to_le_bytes()) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "bad local header",
            ));
        }
        let l_name = u16::from_le_bytes([data[offset + 26], data[offset + 27]]) as usize;
        let l_extra = u16::from_le_bytes([data[offset + 28], data[offset + 29]]) as usize;
        let payload = &data[offset + 30 + l_name + l_extra..offset + 30 + l_name + l_extra + csize];
        let raw = if method == 0 {
            payload.to_vec()
        } else {
            let mut dec = flate2::write::DeflateDecoder::new(Vec::new());
            dec.write_all(payload)?;
            dec.finish()?
        };
        // entry paths are refused when they leave the target folder
        if name.contains("..") {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "bad entry name",
            ));
        }
        let mut target = dst.to_path_buf();
        for part in name.split('/') {
            if part.is_empty() || part == "." {
                continue;
            }
            target.push(part);
        }
        if name.ends_with('/') {
            let _ = std::fs::create_dir_all(&target);
            continue;
        }
        if let Some(parent) = target.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&target, raw)?;
    }
    Ok(())
}

/// Duplicate FOLDER with all its contents (M4-G43 with a folder
/// reference on the left side).
fn copy_dir_all(src: &std::path::Path, dst: &std::path::Path) -> std::io::Result<()> {
    std::fs::create_dir_all(dst)?;
    let items = std::fs::read_dir(src)?.collect::<Result<Vec<_>, _>>()?;
    for e in items {
        let t = dst.join(e.file_name());
        let p = e.path();
        if p.is_dir() {
            copy_dir_all(&p, &t)?;
        } else {
            std::fs::copy(&p, &t)?;
        }
    }
    Ok(())
}
