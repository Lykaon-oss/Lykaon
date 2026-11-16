//! Lykaon compiler - M1a (syntax only).
//! Lexer, sentence splitter, name pre-scan, parser, formatter, M1a diagnostics.

pub mod cli;
pub mod codegen;
pub mod coverage_map;
pub mod diagnostics;
pub mod formatter;
pub mod interp;
pub mod lexer;
pub mod linker;
pub mod optimizer;
pub mod packages;
pub mod parser;
pub mod pre_scan;
pub mod prover;
pub mod sem;
pub mod splitter;
pub mod wpo;

// The MIR block graph lives in lykaon-core (the generator suspension runs it);
// the name stays available here for the M1b callers of compile_mir.
pub use lykaon_core::mir;
// M4-8 (Appendix K 7.10/7.11): the tool-argument parser and the signal
// flags are lykaon-core items; the runner and the built program use them.
pub use lykaon_core::args;
pub use lykaon_core::signals;

use std::path::{Path, PathBuf};

// Public entry points used by the CLI and tests.

/// Check a source file: lex, split into sentences, pre-scan names, parse.
/// Returns the diagnostic output text and whether the check succeeded (no errors).
pub fn check_source(source: &str, file_name: &str) -> (String, bool) {
    let diagnostics = check_source_diagnostics(source, file_name);
    let has_error = diagnostics
        .iter()
        .any(|d| d.severity == diagnostics::Severity::Error);
    let out = diagnostics
        .iter()
        .map(|d| d.to_string())
        .collect::<Vec<_>>()
        .join("\n");
    let out = if out.is_empty() {
        String::new()
    } else {
        out + "\n"
    };
    (out, !has_error)
}

/// Check a file's bytes (T0018): a file that is not UTF-8 is refused before
/// any lexing, so the check command reports the book's wording instead of a
/// generic read error. A BOM is ignored, as the splitter does.
pub fn check_bytes(bytes: &[u8], file_name: &str) -> (String, bool) {
    let body = bytes.strip_prefix(&[0xEF, 0xBB, 0xBF][..]).unwrap_or(bytes);
    match std::str::from_utf8(body) {
        Ok(source) => check_source(source, file_name),
        Err(_) => {
            // the Where line shows what could be read, so the person can
            // find the line: the lossy text keeps the valid prefix
            let seen = String::from_utf8_lossy(body);
            let line1 = seen.lines().next().unwrap_or("").to_string();
            let d = diagnostics::Diagnostic::error(
                "T0018",
                "The file is not UTF-8.".to_string(),
                file_name.to_string(),
                1,
                line1,
                0,
                0,
                "The file holds bytes that are not valid UTF-8.".to_string(),
                "Save the file as UTF-8.".to_string(),
            );
            (d.to_string() + "\n", false)
        }
    }
}

/// The diagnostics of a source file as structured values. The text form
/// (`check_source`) draws the caret line itself; the UI bridge needs the
/// line and the byte range separately so the editor can place a marker.
pub fn diagnostics(source: &str, file_name: &str) -> Vec<diagnostics::Diagnostic> {
    check_source_diagnostics(source, file_name)
}

fn check_source_diagnostics(source: &str, file_name: &str) -> Vec<diagnostics::Diagnostic> {
    match compile(source, file_name) {
        Compiled::Diags(d) => d,
        Compiled::Ready(_) => {
            // the compile returns Ready when only warnings were found;
            // collect them from the splitter (the same warnings the
            // compile saw)
            splitter::split_source(source, file_name)
                .map(|s| s.diagnostics)
                .unwrap_or_default()
        }
    }
}

enum Compiled {
    Diags(Vec<diagnostics::Diagnostic>),
    Ready(sem::Program),
}

/// Names defined by used modules but not shared (ch.36): name -> module stem.
/// Using one from outside is T0208, not T0205.
thread_local! {
    static UNSHARED: std::cell::RefCell<Vec<(String, String)>> = std::cell::RefCell::new(Vec::new());
}

pub(crate) fn unshared_module_of(name: &str) -> Option<String> {
    UNSHARED.with(|u| {
        u.borrow()
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, m)| m.clone())
    })
}

/// Lex, split, pre-scan, parse, then build the typed tree. Any syntax error
/// means the later stages do not run.
fn compile(source: &str, file_name: &str) -> Compiled {
    // M3b: the contract prover's run-time hook (Ensures skips) installs once
    // per process, from the single compile funnel, so the interpreter, the
    // test runs and liblykaon_rt's embedded evaluator all see it.
    prover::install();
    let source = match expand_uses(source, file_name, &mut Vec::new(), 1) {
        Ok(s) => s,
        Err(d) => return Compiled::Diags(vec![d]),
    };
    let split = match splitter::split_source(&source, file_name) {
        Ok(s) => s,
        Err(e) => return Compiled::Diags(e),
    };
    let names = pre_scan::collect_names(&split.all, &split.roots);
    let mut diags = split.diagnostics;
    diags.extend(parser::parse_block(
        &split.all,
        &split.roots,
        &names,
        file_name,
        false,
    ));
    let has_error = diags
        .iter()
        .any(|d| d.severity == diagnostics::Severity::Error);
    if has_error {
        return Compiled::Diags(diags);
    }
    let (program, sem_diags) = sem::build(&split.all, &split.roots, &names, file_name);
    if !sem_diags.is_empty() {
        diags.extend(sem_diags);
        return Compiled::Diags(diags);
    }
    if std::env::var("Lykaon_DEBUG").is_ok() {
        eprintln!("DBG funcs: {:#?}", program.funcs);
    }
    Compiled::Ready(program)
}

/// Compile to the typed tree for callers outside the pipeline (liblykaon_rt's
/// embedded evaluator parses the embedded source with this same front end).
pub fn compile_tree(
    source: &str,
    file_name: &str,
) -> Result<sem::Program, Vec<diagnostics::Diagnostic>> {
    match compile(source, file_name) {
        Compiled::Diags(d) => Err(d),
        Compiled::Ready(prog) => Ok(prog),
    }
}

/// Compile to the old MIR graph (kept for M1b callers; M3's optimizer runs
/// on the typed tree instead, see `optimizer::optimize_tree` — the MIR
/// graph stays the fresh build here).
pub fn compile_mir(
    source: &str,
    file_name: &str,
) -> Result<mir::ProgramMir, Vec<diagnostics::Diagnostic>> {
    match compile(source, file_name) {
        Compiled::Diags(d) => Err(d),
        Compiled::Ready(prog) => Ok(mir::build(&prog)),
    }
}

/// Expand `Use <name>.` sentences (ch.36) by splicing the used module's
/// shared definitions in front of the file, so the whole existing pipeline
/// (name pre-scan, parse, types) sees them. Returns the merged source.
fn expand_uses(
    source: &str,
    file_name: &str,
    visited: &mut Vec<std::path::PathBuf>,
    line_no: usize,
) -> Result<String, diagnostics::Diagnostic> {
    if visited.is_empty() {
        UNSHARED.with(|u| u.borrow_mut().clear());
        // the entry file itself counts as visited, so a module that uses it
        // back is a cycle (T0210)
        if let Ok(c) = std::fs::canonicalize(file_name) {
            visited.push(c);
        }
    }
    let dir = std::path::Path::new(file_name)
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_default();
    let mut out = String::new();
    let mut line = line_no;
    for raw in source.lines() {
        let t = raw.trim();
        if t.to_ascii_lowercase().starts_with("use ") && t.ends_with('.') {
            // module name: words after "use"; `Use sales from reports.` -> reports/sales
            let words: Vec<&str> = t[..t.len() - 1].split_whitespace().skip(1).collect();
            // M4-G17 (Appendix K 7.3): ``Use NUMBER workers.`` is a Spread
            // worker count, not a module; chapter 36's module Use reads
            // only words, so a leading whole number passes through to the
            // worker-count shape check.
            if words.first().map(|w| w.parse::<u64>().is_ok()) == Some(true) {
                out.push_str(raw);
                out.push('\n');
                line += 1;
                continue;
            }
            // M4-G58 (Appendix K 7.7): ``Use seed N.`` sets the random
            // generator, not a module (the reserved word seed cannot
            // start a module path - logged).
            if words.len() >= 2
                && words.first().map(|w| w.eq_ignore_ascii_case("seed")) == Some(true)
                && words[1].parse::<u64>().is_ok()
            {
                out.push_str(raw);
                out.push('\n');
                line += 1;
                continue;
            }
            // M4-S88 (Appendix K 7.12): ``Use log level LEVEL.`` sets the
            // run's log level, not a module (the reserved words log and
            // level cannot start a module path).
            if words.len() >= 2
                && words.first().map(|w| w.eq_ignore_ascii_case("log")) == Some(true)
                && words[1].eq_ignore_ascii_case("level")
            {
                out.push_str(raw);
                out.push('\n');
                line += 1;
                continue;
            }
            let mut head: Vec<&str> = Vec::new();
            let mut tail: Vec<&str> = Vec::new();
            let mut in_from = false;
            for w in words {
                if w.eq_ignore_ascii_case("from") {
                    in_from = true;
                } else if in_from {
                    tail.push(w);
                } else {
                    head.push(w);
                }
            }
            let module = if tail.is_empty() {
                head.join(" ")
            } else {
                format!("{}/{}", tail.join(" "), head.join(" "))
            };
            let module = module.to_ascii_lowercase().replace(' ', "_");
            let mut candidates: Vec<std::path::PathBuf> = Vec::new();
            if !module.contains('/') {
                if let Some(d) = dir.to_str() {
                    candidates.push(std::path::Path::new(d).join(format!("{module}.lykaon")));
                }
            }
            candidates.push(std::path::PathBuf::from(format!("{module}.lykaon")));
            let found = candidates.iter().find(|p| p.is_file()).cloned();
            let Some(path) = found else {
                return Err(diagnostics::Diagnostic::error(
                    "T0209",
                    "A file is used but cannot be found.".to_string(),
                    file_name.to_string(),
                    line,
                    raw.to_string(),
                    0,
                    raw.len(),
                    format!("There is no file {module}.lykaon where Lykaon looks."),
                    "Create the file, or check the spelling of the module name.".to_string(),
                ));
            };
            let path = std::fs::canonicalize(&path).unwrap_or(path);
            if visited.iter().any(|p| p == &path) {
                return Err(diagnostics::Diagnostic::error(
                    "T0210",
                    "Modules use each other in a circle.".to_string(),
                    file_name.to_string(),
                    line,
                    raw.to_string(),
                    0,
                    raw.len(),
                    "A cycle of Use sentences never finishes loading.".to_string(),
                    "Remove one Use from the circle.".to_string(),
                ));
            }
            visited.push(path.clone());
            let module_text = std::fs::read_to_string(&path).unwrap_or_default();
            let module_path = path.to_string_lossy().to_string();
            let expanded = expand_uses(&module_text, &module_path, visited, 1)?;
            out.push_str(&shared_source_of(&expanded, &module_path));
            visited.pop();
        } else {
            out.push_str(raw);
            out.push('\n');
        }
        line += 1;
    }
    Ok(out)
}

/// The source text of one module's shared definitions (ch.36): sentences whose
/// name was marked with `Share`, or every definition when the file is the
/// settings module. A subtree is copied by line range, which works because a
/// definition and its indented body are contiguous in the source.
fn shared_source_of(source: &str, file_name: &str) -> String {
    let Ok(split) = splitter::split_source(source, file_name) else {
        return String::new();
    };
    let is_settings = std::path::Path::new(file_name)
        .file_stem()
        .map(|s| s.eq_ignore_ascii_case("settings"))
        .unwrap_or(false);
    // collect shared names from `Share <name>.` sentences
    let mut shared: Vec<String> = Vec::new();
    for &r in &split.roots {
        let text = &split.all[r].text;
        let low = text.to_ascii_lowercase();
        if low.starts_with("share ") {
            let name: String = low[6..low.len().saturating_sub(1)]
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ");
            if !name.is_empty() {
                shared.push(name);
            }
        }
    }
    // subtree line ranges: root k covers its lines up to the next root
    let mut ranges: Vec<(usize, usize, &str)> = Vec::new(); // (start, end, root text)
    let mut roots_by_line: Vec<(usize, usize)> = split
        .roots
        .iter()
        .map(|&r| (split.all[r].line, r))
        .collect();
    roots_by_line.sort_unstable();
    for (k, &(start, r)) in roots_by_line.iter().enumerate() {
        let end = roots_by_line
            .get(k + 1)
            .map(|&(n, _)| n)
            .unwrap_or(source.lines().count() + 1);
        ranges.push((start, end, &split.all[r].text));
    }
    let lines: Vec<&str> = source.lines().collect();
    let stem = std::path::Path::new(file_name)
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();
    let mut out = String::new();
    for (start, end, root_text) in ranges {
        let low = root_text.to_ascii_lowercase();
        // the name this root defines, if any (ch.36: functions and values)
        let defined: Option<String> = if low.starts_with("to ") {
            let after_to: Vec<&str> = low[3..].split_whitespace().collect();
            after_to
                .first()
                .map(|w| w.trim_end_matches('.').to_string())
        } else {
            let mut words: Vec<&str> = low.split_whitespace().collect();
            if words.first() == Some(&"changeable") || words.first() == Some(&"constant") {
                words.remove(0);
            }
            if let Some(pos) = words.iter().position(|w| *w == "is") {
                Some(words[..pos].join(" "))
            } else {
                None
            }
        };
        let keep = if is_settings {
            true
        } else if low.starts_with("share ") || low.starts_with("use ") {
            false
        } else if low.starts_with("to ") {
            let after_to: Vec<&str> = low[3..].split_whitespace().collect();
            shared.iter().any(|n| starts_with_phrase(&after_to, n))
        } else if let Some(name) = &defined {
            shared.iter().any(|n| n == name)
        } else {
            false
        };
        if keep {
            for l in &lines[start.saturating_sub(1)..end.saturating_sub(1)] {
                out.push_str(l);
                out.push('\n');
            }
        } else if let Some(name) = defined {
            // visible-but-not-shared: using it from outside is T0208 (ch.36)
            UNSHARED.with(|u| u.borrow_mut().push((name, stem.clone())));
        }
    }
    out
}

/// Whether the word list begins with the words of `phrase`.
fn starts_with_phrase(words: &[&str], phrase: &str) -> bool {
    let parts: Vec<&str> = phrase.split_whitespace().collect();
    if parts.is_empty() || words.len() < parts.len() {
        return false;
    }
    words[..parts.len()] == parts[..]
}

/// `lykaon test` (ch.38): compile, run every Test block, print one line per test.
pub fn test_source(source: &str, file_name: &str, stdin_text: &str) -> (String, bool) {
    match compile(source, file_name) {
        Compiled::Diags(d) => {
            let out = d
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            (
                if out.is_empty() {
                    String::new()
                } else {
                    out + "\n"
                },
                false,
            )
        }
        Compiled::Ready(prog) => {
            let mut report = String::new();
            let mut all_ok = true;
            for t in &prog.tests {
                match interp::run_test(&prog, &t.body, stdin_text) {
                    Err(e) => {
                        all_ok = false;
                        report.push_str(&format!("{} failed - {}\n", t.name, e.message));
                    }
                    Ok(failed) if failed.is_empty() => {
                        report.push_str(&format!("{} passed\n", t.name));
                    }
                    Ok(failed) => {
                        all_ok = false;
                        report.push_str(&format!("{} failed\n", t.name));
                        for m in failed {
                            report.push_str(&format!("    {m}\n"));
                        }
                    }
                }
            }
            (report, all_ok)
        }
    }
}

/// Run a source file with `lykaon run`: print diagnostics first if any, then
/// the program output. Returns (output text, exit code).
pub fn run_source(source: &str, file_name: &str, stdin_text: &str) -> (String, i32) {
    run_source_budgeted(source, file_name, stdin_text, 0)
}

/// Same as run_source with an interpreter step budget (used by the fuzzer).
pub fn run_source_budgeted(
    source: &str,
    file_name: &str,
    stdin_text: &str,
    budget: u64,
) -> (String, i32) {
    match compile(source, file_name) {
        Compiled::Diags(diags) => {
            let out = diags
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            (
                if out.is_empty() {
                    String::new()
                } else {
                    out + "\n"
                },
                1,
            )
        }
        Compiled::Ready(program) => {
            // the harnesses simulate a person (Ask reads the piped text);
            // no command line: a required Takes reads as bad usage
            match interp::run_budgeted(&program, stdin_text, budget, &[], true) {
                Ok(out) => (out, 0),
                Err(e) => {
                    if e.message.is_empty() {
                        (e.out, e.code)
                    } else {
                        (format!("{}\n", e.message), e.code)
                    }
                }
            }
        }
    }
}

/// M4-8 (Appendix K 7.11): run with the tool's own arguments. The Takes
/// and Option values are parsed against the program's declarations
/// (M4-S82): `help`/`--help` first gives the usage text and exit 0
/// (M4-S84); bad usage gives it and exit 2 (M4-S83). `interactive` says a
/// person can be at the other end of standard input (M4-S86).
pub fn run_source_tool(
    source: &str,
    file_name: &str,
    stdin_text: &str,
    argv: &[String],
    interactive: bool,
) -> (String, i32) {
    let (merged, _, code) =
        run_source_tool_streams(source, file_name, stdin_text, argv, interactive);
    (merged, code)
}

/// M4-9 (7.12): the same run, also returning the byte ranges of the
/// merged output that are standard error (M4-D11/D12) for the front end
/// that writes the two streams for real.
pub fn run_source_tool_streams(
    source: &str,
    file_name: &str,
    stdin_text: &str,
    argv: &[String],
    interactive: bool,
) -> (String, Vec<(usize, usize)>, i32) {
    match compile(source, file_name) {
        Compiled::Diags(diags) => {
            let out = diags
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            (
                if out.is_empty() {
                    String::new()
                } else {
                    out + "\n"
                },
                Vec::new(),
                1,
            )
        }
        Compiled::Ready(program) => {
            // the usage text's NAME: the file name without its extension
            let name = std::path::Path::new(file_name)
                .file_stem()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_else(|| file_name.to_string());
            match lykaon_core::args::parse_tool_args(&program, &name, argv) {
                lykaon_core::args::ToolArgs::Help(text) => (text, Vec::new(), 0),
                lykaon_core::args::ToolArgs::Bad(e) => (format!("{}\n", e.text), Vec::new(), 2),
                lykaon_core::args::ToolArgs::Bindings(bindings) => {
                    let (result, ranges) = interp::run_budgeted_streams(
                        &program,
                        stdin_text,
                        0,
                        &bindings,
                        interactive,
                    );
                    let (out, code) = match result {
                        Ok(out) => (out, 0),
                        Err(e) => {
                            if e.message.is_empty() {
                                (e.out, e.code)
                            } else {
                                (format!("{}\n", e.message), e.code)
                            }
                        }
                    };
                    (out, ranges, code)
                }
            }
        }
    }
}

/// Format source to the canonical layout.
pub fn format_source(source: &str) -> String {
    formatter::format(source)
}

/// Compile a source file to a native object file, reporting which lowering
/// the program received: `Full` (scalar machine code from the typed tree) or
/// `Embedded` (an object whose `lykaon_main` runs the embedded source through
/// the evaluator of lykaon-core). Diagnostics are returned as the error text.
/// The linker + runner (`lykaon run --native`, `lykaon build`) wrap this.
pub fn native_object(
    source: &str,
    file_name: &str,
    mode: &str,
) -> Result<(Vec<u8>, codegen::LowerKind, Vec<optimizer::PassReport>), NativeFail> {
    match compile(source, file_name) {
        Compiled::Diags(diags) => {
            let text = diags
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            Err(NativeFail::Diags(if text.is_empty() {
                text
            } else {
                text + "\n"
            }))
        }
        Compiled::Ready(mut prog) => {
            // fast and small builds run the typed-tree passes first
            // (M3-D6); debug keeps the freshly compiled tree
            let reports = optimizer::optimize_tree(&mut prog, mode);
            codegen::Codegen::build_object(source, &prog, mode)
                .map(|(obj, kind)| (obj, kind, reports))
                .map_err(NativeFail::Tool)
        }
    }
}

/// Why a native build could not produce a runnable program: `Diags` are the
/// compiler's own messages for the user (printed to the console like the
/// interpreter's), `Tool` is everything the toolchain did wrong.
pub enum NativeFail {
    Diags(String),
    Tool(String),
}

impl NativeFail {
    pub fn message(&self) -> &str {
        match self {
            NativeFail::Diags(t) => t,
            NativeFail::Tool(t) => t,
        }
    }
}

/// Compile to machine code and run it (M3 backend, section 9): write the
/// object, link it with liblykaon_rt and the Microsoft x64 toolchain, execute
/// the built program, and return its exit code.
/// Compile to machine code, link, run, and return the exit code together
/// with the captured stdout (so `lykaon run --native` can print it).
pub fn native_run(source: &str, file_name: &str, mode: &str) -> Result<(i32, String), NativeFail> {
    native_run_captured(source, file_name, mode)
}

/// Compile to machine code, link, run, and capture stdout together with the
/// exit code (used by the differential test harness).
pub fn native_run_captured(
    source: &str,
    file_name: &str,
    mode: &str,
) -> Result<(i32, String), NativeFail> {
    let (obj, _kind, _reports) = native_object(source, file_name, mode)?;
    // parallel worker threads of one test process share its pid: a global
    // counter keeps the object and exe file names unique
    static CALL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let n = CALL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let tmp = std::env::temp_dir();
    let obj_path = tmp.join(format!("lykaon_{}_{}.obj", std::process::id(), n));
    let exe_path = tmp.join(format!("lykaon_{}_{}.exe", std::process::id(), n));
    std::fs::write(&obj_path, &obj)
        .map_err(|e| NativeFail::Tool(format!("cannot write {}: {e}", obj_path.display())))?;
    let result = linker::find_rt_lib()
        .map_err(|e| NativeFail::Tool(format!("the runtime library is missing: {e}")))
        .and_then(|rt_lib| linker::link(&obj_path, &rt_lib, &exe_path).map_err(NativeFail::Tool))
        .and_then(|()| {
            // the module system resolves `Use <name>` relative to the
            // source's folder, like the interpreter does with files beside
            // the program (the test programs import their real helpers)
            let mut cmd = std::process::Command::new(&exe_path);
            if let Some(dir) = std::path::Path::new(file_name).parent() {
                // a bare file name has no folder to run from: keep the
                // caller's current directory in that case
                if !dir.as_os_str().is_empty() {
                    cmd.current_dir(dir);
                }
            }
            // the differential harness simulates the person at standard
            // input (M4-S86) exactly as the interpreter harness does - the
            // real console rule lives in the built program itself
            cmd.env("Lykaon_HARNESS_PERSON", "1");
            let out = cmd
                .output()
                .map_err(|e| NativeFail::Tool(format!("cannot run {}: {e}", exe_path.display())))?;
            let code = out.status.code().unwrap_or(1);
            let stdout = String::from_utf8_lossy(&out.stdout).to_string();
            Ok((code, stdout))
        });
    let _ = std::fs::remove_file(&obj_path);
    let _ = std::fs::remove_file(&exe_path);
    result
}

/// M4-D17 (Appendix K 7.11): run native with the program's own arguments.
/// Like native_run_captured, but the built program receives `argv`, the
/// usage-name override (LYKAON_TOOL_NAME: the runner's temporary executable
/// files carry a generated name, and the usage text names the program),
/// and - when the caller's standard input is a terminal - the child
/// inherits it (a person can answer an Ask; M4-S86). Standard output and
/// standard error are captured and returned as text.
pub fn native_run_tool(
    source: &str,
    file_name: &str,
    mode: &str,
    argv: &[String],
) -> Result<(i32, String, String), NativeFail> {
    let (obj, _kind, _reports) = native_object(source, file_name, mode)?;
    static CALL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let n = CALL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let tmp = std::env::temp_dir();
    let obj_path = tmp.join(format!("lykaon_tool_{}_{}.obj", std::process::id(), n));
    let exe_path = tmp.join(format!("lykaon_tool_{}_{}.exe", std::process::id(), n));
    std::fs::write(&obj_path, &obj)
        .map_err(|e| NativeFail::Tool(format!("cannot write {}: {e}", obj_path.display())))?;
    let tool_name = std::path::Path::new(file_name)
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| file_name.to_string());
    let result = linker::find_rt_lib()
        .map_err(|e| NativeFail::Tool(format!("the runtime library is missing: {e}")))
        .and_then(|rt_lib| linker::link(&obj_path, &rt_lib, &exe_path).map_err(NativeFail::Tool))
        .and_then(|()| {
            let mut cmd = std::process::Command::new(&exe_path);
            if let Some(dir) = std::path::Path::new(file_name).parent() {
                if !dir.as_os_str().is_empty() {
                    cmd.current_dir(dir);
                }
            }
            cmd.env("LYKAON_TOOL_NAME", &tool_name).args(argv);
            // the built program reads the caller's standard input (a
            // terminal person answers an Ask, M4-S86; a piped one feeds
            // the input reads) - output captures only out and err
            cmd.stdin(std::process::Stdio::inherit());
            let out = cmd
                .output()
                .map_err(|e| NativeFail::Tool(format!("cannot run {}: {e}", exe_path.display())))?;
            let code = out.status.code().unwrap_or(1);
            let stdout = String::from_utf8_lossy(&out.stdout).to_string();
            let stderr = String::from_utf8_lossy(&out.stderr).to_string();
            Ok((code, stdout, stderr))
        });
    let _ = std::fs::remove_file(&obj_path);
    let _ = std::fs::remove_file(&exe_path);
    result
}
/// return the exe path plus the compile+link wall time in milliseconds.
/// The caller is responsible for deleting the exe. This is used by `lykaon
/// bench` so that compilation happens once, outside the execution timer.
/// Compile `source` to a native exe (compile + link, timed separately) and
/// return the exe path plus the compile+link wall time in milliseconds.
/// The caller is responsible for deleting the exe. This is used by `lykaon
/// bench` so that compilation happens once, outside the execution timer.
pub fn native_compile_to_exe(
    source: &str,
    file_name: &str,
    mode: &str,
    out_dir: &Path,
) -> Result<(PathBuf, f64), NativeFail> {
    let start = std::time::Instant::now();
    let (obj, _kind, _reports) = native_object(source, file_name, mode)?;
    static CALL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let n = CALL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let obj_path = out_dir.join(format!("lykaon_bench_{}_{}.obj", std::process::id(), n));
    let exe_path = out_dir.join(format!("lykaon_bench_{}_{}.exe", std::process::id(), n));
    std::fs::write(&obj_path, &obj)
        .map_err(|e| NativeFail::Tool(format!("cannot write {}: {e}", obj_path.display())))?;
    let rt_lib = linker::find_rt_lib()
        .map_err(|e| NativeFail::Tool(format!("the runtime library is missing: {e}")))?;
    linker::link(&obj_path, &rt_lib, &exe_path).map_err(NativeFail::Tool)?;
    let _ = std::fs::remove_file(&obj_path);
    let compile_ms = start.elapsed().as_secs_f64() * 1000.0;
    Ok((exe_path, compile_ms))
}

/// Run an existing exe and return (exit_code, stdout, elapsed_ms).
pub fn run_exe(exe: &Path) -> Result<(i32, String, f64), NativeFail> {
    let start = std::time::Instant::now();
    let out = std::process::Command::new(exe)
        .output()
        .map_err(|e| NativeFail::Tool(format!("cannot run {}: {e}", exe.display())))?;
    let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;
    let code = out.status.code().unwrap_or(1);
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    Ok((code, stdout, elapsed_ms))
}
