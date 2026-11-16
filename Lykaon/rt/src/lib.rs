//! liblykaon_rt (M3): the runtime library linked into `lykaon build` programs.
//!
//! * The embedded evaluator path (codegen::LowerKind::Embedded): the object's
//!   `lykaon_main` calls `lykaon_rt_main(src, len, mode)` with the program source
//!   embedded as a data symbol. This compiles the source with the same front
//!   end the developer used and runs it with the evaluator of lykaon-core —
//!   the interpreter that defines what every program means — so native
//!   output is byte-exact with `lykaon run` by construction.
//! * The Full path's helpers: buffered output (printed once at program end
//!   by `lykaon_rt_flush`, so an aborting run prints only the fatal line, like
//!   the CLI), the interpreter's exact fatal lines, checked whole
//!   multiplication/negation/power (the runtime side of the M3-S31
//!   contracts), and the decimal rounding that `nearest to` and `as_i64`
//!   use (decimals round half away from zero).
//!
//! Exit semantics copied from the CLI: a fatal interpreter error prints its
//! one message line (with a newline) and exits 1, discarding buffered
//! output; success prints the whole buffer and exits 0.

use std::io::Write;
use std::sync::Mutex;

/// Buffered program output, printed by lykaon_rt_flush (Full path) or by
/// lykaon_rt_main (embedded path) at program end.
static OUT: Mutex<String> = Mutex::new(String::new());

fn with_out(f: impl FnOnce(&mut String)) {
    let mut b = OUT.lock().unwrap_or_else(|p| p.into_inner());
    f(&mut b);
}

fn emit(s: &str, without: bool) {
    with_out(|b| {
        b.push_str(s);
        if !without {
            b.push('\n');
        }
    });
}

/// Print a fatal line and exit 1 discarding the buffer: the CLI prints the
/// fatal message alone (interp Err(Fatal) -> run_source's
/// `(format!("{}\n", e.message), 1)`) and drops everything printed before.
fn fail(msg: &str) -> ! {
    with_out(|b| b.clear());
    print!("{msg}\n");
    let _ = std::io::stdout().flush();
    std::process::exit(1)
}

// ---------------------------------------------------------------- says

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_say_whole(x: i64, without: i64) {
    emit(&x.to_string(), without != 0);
}

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_say_dec(bits: i64, places: i64, without: i64) {
    let x = f64::from_bits(bits as u64);
    emit(
        &lykaon_core::interp::format_decimal(x, places.max(0) as usize),
        without != 0,
    );
}

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_say_bool(b: i64, without: i64) {
    emit(if b != 0 { "yes" } else { "no" }, without != 0);
}

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_say_text(ptr: *const u8, len: i64, without: i64) {
    let text = unsafe_text(ptr, len);
    emit(text, without != 0);
}

fn unsafe_text<'a>(ptr: *const u8, len: i64) -> &'a str {
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len.max(0) as usize) };
    std::str::from_utf8(bytes).unwrap_or("missing")
}

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_fail(ptr: *const u8, len: i64) {
    let msg = unsafe_text(ptr, len);
    fail(msg);
}

// --------------------------------------------------- whole number runs

const T0603: &str =
    "Error: A whole number went past 64 bits. (T0603)\nFix: Use big number or checked plus.";
const T0604: &str = "Error: A whole number was divided by zero. (T0604)\nFix: Check the divisor.";

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_mul_whole(a: i64, b: i64) -> i64 {
    // interp.rs bin_op Op::Time: x.checked_mul(y) -> fatal T0603
    match a.checked_mul(b) {
        Some(v) => v,
        None => fail(T0603),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_neg_whole(a: i64) -> i64 {
    // interp.rs Op negation: x.checked_neg() -> fatal T0603
    match a.checked_neg() {
        Some(v) => v,
        None => fail(T0603),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_pow_whole(x: i64, y: i64) -> i64 {
    // interp.rs E::Pow exactly: y<0 -> 0, x==0 -> 0, x==1 -> 1, x==-1 ->
    // parity, y>62 -> fatal T0603, else a checked_mul loop -> fatal T0603
    if y < 0 {
        return 0;
    }
    if x == 0 {
        return 0;
    }
    if x == 1 {
        return 1;
    }
    if x == -1 {
        return if y % 2 == 0 { 1 } else { -1 };
    }
    if y > 62 {
        fail(T0603);
    }
    let mut acc: i64 = 1;
    for _ in 0..y {
        match acc.checked_mul(x) {
            Some(v) => acc = v,
            None => fail(T0603),
        }
    }
    acc
}

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_round_dec(bits: i64, even: i64) -> i64 {
    // interp.rs E::Round: round () or nearest to even (), then `as i64`
    // (value.clamp, which saturates)
    let x = f64::from_bits(bits as u64);
    if even != 0 {
        x.round_ties_even() as i64
    } else {
        x.round() as i64
    }
}

/// Wrapping and saturating whole math (ch.19) that cannot fail. op codes:
/// 0 wrap +, 1 wrap -, 2 wrap *, 3 saturating +, 4 saturating -, 5
/// saturating *.
#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_wrap_whole(op: i64, a: i64, b: i64) -> i64 {
    match op {
        0 => a.wrapping_add(b),
        1 => a.wrapping_sub(b),
        2 => a.wrapping_mul(b),
        3 => a.saturating_add(b),
        4 => a.saturating_sub(b),
        5 => a.saturating_mul(b),
        _ => fail(T0603),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_whole_divided_by(a: i64, b: i64) -> i64 {
    // interp.rs E::DivWhole: y == 0 is fatal T0604; otherwise x / y. Note
    // that i64::MIN / -1 panics inside the interpreter too (the process
    // dies with nothing flushed), so exit 101 with an empty buffer matches.
    if b == 0 {
        fail(T0604);
    }
    if b == -1 && a == i64::MIN {
        std::process::exit(101);
    }
    a / b
}

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_whole_rem(a: i64, b: i64) -> i64 {
    // interp.rs E::Rem, same corners as whole divided by
    if b == 0 {
        fail(T0604);
    }
    if b == -1 && a == i64::MIN {
        std::process::exit(101);
    }
    a % b
}

// ------------------------------------------------------------- control

#[unsafe(no_mangle)]
pub extern "C" fn lykaon_rt_flush() {
    let text = {
        let mut b = OUT.lock().unwrap_or_else(|p| p.into_inner());
        std::mem::take(&mut *b)
    };
    print!("{text}");
    let _ = std::io::stdout().flush();
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn lykaon_rt_main(src: *const u8, len: i64, mode: i64) -> i64 {
    // SAFETY: src/len come from the generated program's own static data
    // (the embedded source), which outlives the call.
    let bytes = unsafe { std::slice::from_raw_parts(src, len.max(0) as usize) };
    let source = match std::str::from_utf8(bytes) {
        Ok(s) => s,
        Err(_) => fail("internal: the embedded source is not valid text"),
    };
    let prog = match lykaon::compile_tree(source, "program.lykaon") {
        Ok(p) => p,
        Err(diags) => {
            let text = diags
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            print!("{text}\n");
            let _ = std::io::stdout().flush();
            std::process::exit(1);
        }
    };
    // M3-S37: contracts are debug-only; fast and small builds drop them
    // unless the author wrote `checked`.
    let mut prog = prog;
    if mode == 1 || mode == 2 {
        for f in &mut prog.funcs {
            f.requires.retain(|c| c.checked);
            f.ensures.retain(|c| c.checked);
        }
        lykaon_rt_strip(&mut prog);
        // the typed-tree passes run here too, so an embedded fast/small
        // build and a full fast/small build make the same trade (M3-D6)
        let _ =
            lykaon::optimizer::optimize_tree(&mut prog, if mode == 1 { "fast" } else { "small" });
    }
    run_prog(&prog)
}

/// Run the compiled program with the evaluator of lykaon-core, printing the
/// output exactly as the CLI does (out as-is, or message + newline, exit 1).
fn run_prog(prog: &lykaon::sem::Program) -> i64 {
    // the CLI reads stdin fully before running (Ask slides through it
    // lazily); only programs that can read stdin at all read it, so a
    // no-input program never sits waiting on a terminal
    let stdin_text = read_stdin_if_ask(prog);
    // M4-8 (M4-S86): standard input is the real console of the built
    // program; when it is not a terminal, Ask fails with "no person here".
    // The test harnesses simulate the person instead (they run with no
    // console at all): Lykaon_HARNESS_PERSON=1 says a person is at the
    // other end, the same rule the interpreter harnesses use.
    let interactive = std::io::IsTerminal::is_terminal(&std::io::stdin())
        || std::env::var("Lykaon_HARNESS_PERSON").as_deref() == Ok("1");
    // M4-8 (M4-S79): arm the signals once per process, so a signal with no
    // block still ends the program after cleaning up.
    arm_signals();
    // M4-8 (M4-S82): the built program parses its own arguments against
    // its Takes and Option declarations. The usage text's NAME is
    // argv[0]'s stem (the installed program's name), or the
    // LYKAON_TOOL_NAME override the runner sets (its temporary executable
    // files carry a generated name).
    let argv: Vec<String> = CLI_ARGS
        .lock()
        .map(|g| g.iter().skip(1).cloned().collect())
        .unwrap_or_default();
    let name = tool_name_from_argv();
    match lykaon::args::parse_tool_args(prog, &name, &argv) {
        lykaon::args::ToolArgs::Help(text) => {
            // M4-S84: help prints the usage text and exits with 0.
            print!("{text}");
            let _ = std::io::stdout().flush();
            0
        }
        lykaon::args::ToolArgs::Bad(e) => {
            // M4-S83: bad usage prints the usage text and exits with 2.
            eprint!("{}", e.text);
            2
        }
        lykaon::args::ToolArgs::Bindings(bindings) => {
            let (result, ranges) =
                lykaon::interp::run_budgeted_streams(prog, &stdin_text, 0, &bindings, interactive);
            let (merged, code) = match result {
                Ok(out) => (out, 0),
                Err(e) => {
                    if e.message.is_empty() {
                        (e.out, e.code)
                    } else {
                        (format!("{}\n", e.message), e.code)
                    }
                }
            };
            // M4-D11 (7.12): Log lines belong to standard error; the
            // ranges split the one merged stream, in order.
            let (stdout_text, stderr_text) = lykaon::interp::split_streams(&merged, &ranges);
            print!("{stdout_text}");
            eprint!("{stderr_text}");
            let _ = std::io::stdout().flush();
            code as i64
        }
    }
}

/// M4-8: the usage text's NAME: the LYKAON_TOOL_NAME environment override
/// (set by the runner for its temporary executables), else argv[0]'s file
/// stem, else a plain fallback.
fn tool_name_from_argv() -> String {
    if let Ok(n) = std::env::var("LYKAON_TOOL_NAME") {
        if !n.is_empty() {
            return n;
        }
    }
    if let Ok(g) = CLI_ARGS.lock() {
        if let Some(a0) = g.first() {
            if let Some(stem) = std::path::Path::new(a0).file_stem() {
                return stem.to_string_lossy().to_string();
            }
        }
    }
    "program".to_string()
}

/// The built program reads stdin fully before running (Ask slides through
/// it lazily); only programs that can read stdin at all read it, so a
/// no-input program never sits waiting on a terminal. Nested bodies count
/// (an Ask inside an If. runs only when its branch runs); M4-8 adds the
/// For each line in input. blocks and any read input expression.
fn read_stdin_if_ask(prog: &lykaon::sem::Program) -> String {
    if !can_read_stdin(prog) {
        return String::new();
    }
    let mut buf = String::new();
    use std::io::Read;
    let _ = std::io::stdin().lock().read_to_string(&mut buf);
    buf
}

fn can_read_stdin(prog: &lykaon::sem::Program) -> bool {
    let found = std::cell::Cell::new(false);
    let mut scan = |e: &lykaon::sem::Expr| {
        // the walk hands the statement's whole expressions; the read can
        // sit nested (a Say of the read), so the scan descends
        if input_in_expr(e) {
            found.set(true);
        }
    };
    for st in &prog.body {
        // the read-only expression walk covers every nested body and
        // expression shape (exhaustive in the compiler)
        lykaon::wpo::read_stmt_exprs(st, &mut scan);
        if asks_in(std::slice::from_ref(st)) {
            found.set(true);
        }
    }
    for f in &prog.funcs {
        match &f.body {
            lykaon::sem::FnBody::Block(b) => {
                for st in b {
                    lykaon::wpo::read_stmt_exprs(st, &mut scan);
                    if asks_in(std::slice::from_ref(st)) {
                        found.set(true);
                    }
                }
            }
            lykaon::sem::FnBody::Expr(e) => {
                if input_in_expr(e) {
                    found.set(true);
                }
            }
        }
    }
    found.get()
}

/// M4-8: does the expression hold a read input (or one nested in a
/// sub expression)? The prover's children walk is exhaustive over the
/// expression shapes.
fn input_in_expr(e: &lykaon::sem::Expr) -> bool {
    if matches!(e.e, lykaon::sem::E::ReadInput) {
        return true;
    }
    lykaon::prover::children(e).iter().any(|c| input_in_expr(c))
}

/// The built program's own command line (argv without argv[0]), copied
/// out of the C argv by main (M4-S82: the Takes and Option values).
static CLI_ARGS: Mutex<Vec<String>> = Mutex::new(Vec::new());

fn asks_in(stmts: &[lykaon::sem::Stmt]) -> bool {
    for s in stmts {
        match s {
            lykaon::sem::Stmt::Ask { .. } => return true,
            // M4-8 (Appendix K 7.11): For each line in input. reads stdin
            // itself; the Run arguments and the other new bodies can hold
            // an Ask or a read input of their own.
            lykaon::sem::Stmt::ForEachInput { body, .. } => {
                if asks_in(body) {
                    return true;
                }
            }
            lykaon::sem::Stmt::WhenSignal { body, .. } => {
                if asks_in(body) {
                    return true;
                }
            }
            lykaon::sem::Stmt::RunProc { args, .. } => {
                if args.iter().any(input_in_expr) {
                    return true;
                }
            }
            lykaon::sem::Stmt::Exit { .. } => {}
            lykaon::sem::Stmt::If { branches, other } => {
                if branches.iter().any(|(_, b)| asks_in(b)) {
                    return true;
                }
                if let Some(ob) = other {
                    if asks_in(ob) {
                        return true;
                    }
                }
            }
            lykaon::sem::Stmt::RepeatTimes { body, .. }
            | lykaon::sem::Stmt::RepeatForever { body }
            | lykaon::sem::Stmt::RepeatWhile { body, .. }
            | lykaon::sem::Stmt::ForRange { body, .. }
            | lykaon::sem::Stmt::ForIn { body, .. }
            | lykaon::sem::Stmt::Test { body, .. }
            | lykaon::sem::Stmt::Check { body, .. } => {
                if asks_in(body) {
                    return true;
                }
            }
            lykaon::sem::Stmt::Try {
                sentence,
                success,
                failure,
            } => {
                if asks_in(std::slice::from_ref(sentence)) || asks_in(success) {
                    return true;
                }
                if failure.iter().any(|(_, b)| asks_in(b)) {
                    return true;
                }
            }
            lykaon::sem::Stmt::LookAt { whens, .. } => {
                if whens.iter().any(|w| asks_in(&w.body)) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// M3-S37 contract stripping goes through every nested body (a Require
/// stated inside a local To. still counts as a contract).
fn lykaon_rt_strip(prog: &mut lykaon::sem::Program) {
    strip_stmts(&mut prog.body);
    for f in &mut prog.funcs {
        if let lykaon::sem::FnBody::Block(b) = &mut f.body {
            strip_stmts(b);
        }
    }
}

fn strip_stmts(stmts: &mut Vec<lykaon::sem::Stmt>) {
    for s in stmts {
        strip_stmt(s);
    }
}

fn strip_stmt(s: &mut lykaon::sem::Stmt) {
    match s {
        lykaon::sem::Stmt::If { branches, other } => {
            for (_, b) in branches {
                strip_stmts(b);
            }
            if let Some(ob) = other {
                strip_stmts(ob);
            }
        }
        lykaon::sem::Stmt::RepeatTimes { body, .. }
        | lykaon::sem::Stmt::RepeatForever { body }
        | lykaon::sem::Stmt::RepeatWhile { body, .. }
        | lykaon::sem::Stmt::ForRange { body, .. }
        | lykaon::sem::Stmt::ForIn { body, .. }
        | lykaon::sem::Stmt::Test { body, .. }
        | lykaon::sem::Stmt::Check { body, .. } => strip_stmts(body),
        lykaon::sem::Stmt::Try {
            sentence,
            success,
            failure,
        } => {
            strip_stmt(sentence);
            strip_stmts(success);
            for (_, b) in failure {
                strip_stmts(b);
            }
        }
        lykaon::sem::Stmt::LookAt { whens, .. } => {
            for w in whens {
                strip_stmts(&mut w.body);
            }
        }
        lykaon::sem::Stmt::DefineLocalFn(f) => {
            f.requires.retain(|c| c.checked);
            f.ensures.retain(|c| c.checked);
            if let lykaon::sem::FnBody::Block(b) = &mut f.body {
                strip_stmts(b);
            }
        }
        _ => {}
    }
}

/// The linked program's entry point comes from the lykaon object at link
/// time; main is the standard console entry (mainCRTStartup).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn main(argc: i32, argv: *const *const u8, _envp: *const *const u8) -> i32 {
    // SAFETY: argv/argc come from the C runtime at process entry.
    // M4-8 (M4-S82): copy the program's own arguments out of the C argv;
    // the Takes and Option spec is parsed in run_prog against the
    // compiled program (the Full lowering carries no tool spec - the
    // compiler gate refuses such a program, so argv reaches the parser).
    if !argv.is_null() && argc > 0 {
        let mut args = Vec::new();
        for i in 0..argc {
            let p = unsafe { *argv.add(i as usize) };
            if p.is_null() {
                break;
            }
            let c = unsafe { std::ffi::CStr::from_ptr(p as *const i8) };
            args.push(c.to_string_lossy().into_owned());
        }
        if let Ok(mut g) = CLI_ARGS.lock() {
            *g = args;
        }
    }
    // M4-8 (M4-S79): arm the signals before anything runs, so a signal
    // with no block still ends the program after cleaning up.
    arm_signals();
    unsafe extern "C" {
        fn lykaon_main() -> i32;
    }
    unsafe { lykaon_main() }
}

/// M4-8 (M4-S79): arm the signal flags once per process (idempotent).
pub fn arm_signals() {
    lykaon::signals::arm();
}
