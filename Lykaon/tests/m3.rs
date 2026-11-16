//! M3 conformance test runner.
//! Walks tests/conformance/m3 and checks:
//!  - valid/*.lykaon parse cleanly (exit 0, empty output)
//!  - errors/*/input.lykaon produce the exact expected.txt (compile diagnostics)
//!  - run/*/input.lykaon run to the exact expected.txt (optional input.txt = stdin)
//!  - runfail/*/input.lykaon fail at runtime: exact expected.txt, exit nonzero
//!  - test/*/input.lykaon run `lykaon test` to the exact expected.txt

use lykaon::{check_source, run_source, test_source};
use std::path::{Path, PathBuf};

const ROOT: &str = "tests/conformance/m3";

fn read(p: &Path) -> String {
    std::fs::read_to_string(p).unwrap_or_else(|e| panic!("cannot read {}: {e}", p.display()))
}

fn walk_cases(kind: &str, failures: &mut Vec<String>, f: impl Fn(&str, &str) -> (String, bool)) {
    let dir = Path::new(ROOT).join(kind);
    if !dir.is_dir() {
        return;
    }
    let mut entries: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.is_dir())
        .collect();
    entries.sort();
    for case in entries {
        let input = case.join("input.lykaon");
        let expected = case.join("expected.txt");
        if !input.is_file() || !expected.is_file() {
            continue;
        }
        let source = read(&input);
        let want = read(&expected).replace('\\', "/").replace("\r\n", "\n");
        let (out, ok) = f(&source, input.to_str().unwrap());
        let out = out.replace('\\', "/").replace("\r\n", "\n");
        // terminal artifacts: the CLI adds a trailing newline
        let want = want.trim_end_matches('\n');
        let out = out.trim_end_matches('\n');
        if !ok {
            failures.push(format!(
                "{kind} {}: expected success, got error:\n{out}",
                case.display()
            ));
        } else if out != want {
            failures.push(format!(
                "{kind} {}: output mismatch.\n--- expected ---\n{:?}\n--- actual ---\n{:?}\n--------------",
                case.display(),
                want,
                out
            ));
        }
    }
}

fn run() {
    let mut failures: Vec<String> = Vec::new();

    /// The interpreter recurses per nested call (T0607 allows 240 nested
    /// calls, which no ordinary test thread holds in debug builds - the
    /// CLI runs it on a roomy worker thread for the same reason). The
    /// conformance runs use the same roomy worker.
    fn run_roomy<T: Send + 'static>(
        source: &str,
        file: &str,
        stdin: &str,
        f: impl Fn(&str, &str, &str) -> T + Send + 'static,
    ) -> T {
        let h = std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn({
                let source = source.to_string();
                let file = file.to_string();
                let stdin = stdin.to_string();
                move || f(&source, &file, &stdin)
            })
            .expect("cannot spawn the conformance worker");
        h.join().expect("the conformance worker panicked")
    }

    // ---- valid: must parse cleanly with no diagnostics ----
    let valid = Path::new(ROOT).join("valid");
    if valid.is_dir() {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(&valid)
            .unwrap()
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().map_or(false, |e| e == "lykaon"))
            .collect();
        entries.sort();
        for p in entries {
            let source = read(&p);
            let (out, ok) = check_source(&source, p.to_str().unwrap());
            if !ok || !out.is_empty() {
                failures.push(format!(
                    "VALID {}: expected clean parse, ok={} output={:?}",
                    p.display(),
                    ok,
                    out
                ));
            }
        }
    }

    // ---- errors: compile must reject with the exact diagnostics ----
    let errors = Path::new(ROOT).join("errors");
    if errors.is_dir() {
        let mut cases: Vec<PathBuf> = std::fs::read_dir(&errors)
            .unwrap()
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.is_dir())
            .collect();
        cases.sort();
        for case in cases {
            let input = case.join("input.lykaon");
            let expected = case.join("expected.txt");
            if !input.is_file() || !expected.is_file() {
                continue;
            }
            let source = read(&input);
            let want = read(&expected).replace('\\', "/").replace("\r\n", "\n");
            let (out, ok) = check_source(&source, input.to_str().unwrap());
            // The Where line of module-cycle diagnostics embeds the canonical
            // absolute path of the source tree, which differs per machine.
            // Normalize it so the suite is location-independent (reproducible
            // builds, ch.67): any absolute path from the project root becomes
            // <root>.
            let canon = std::fs::canonicalize(&input).unwrap_or(input.clone());
            let mut base: PathBuf = canon;
            // the base is the compiler crate folder, named lykaon while the
            // per-folder rename is pending and lykaon afterwards
            while base.file_name().map_or(true, |n| n != "lykaon") {
                match base.parent() {
                    Some(p) if p != base => base = p.to_path_buf(),
                    _ => break,
                }
            }
            let bases = [
                format!("\\\\?\\{}", base.to_string_lossy()),
                base.to_string_lossy().to_string(),
            ];
            let mut out = out.replace('\\', "/").replace("\r\n", "\n");
            for b in bases {
                out = out.replace(&b.replace('\\', "/"), "<root>");
            }
            let want = want.trim_end_matches('\n');
            let out = out.trim_end_matches('\n');
            if ok {
                failures.push(format!(
                    "ERROR {}: expected rejection, but parsed cleanly",
                    case.display()
                ));
            } else if out != want {
                eprintln!("DEBUG ACTUAL: {:?}", out);
                eprintln!("DEBUG WANT: {:?}", want);
                failures.push(format!(
                    "ERROR {}: output mismatch.\n--- expected ---\n{:?}\n--- actual ---\n{:?}\n--------------",
                    case.display(),
                    want,
                    out
                ));
            }
        }
    }

    // ---- run: valid programs with exact stdout ----
    walk_cases("run", &mut failures, |source, name| {
        let stdin = std::fs::read_to_string(Path::new(name).parent().unwrap().join("input.txt"))
            .unwrap_or_default();
        let (out, code) = run_roomy(source, name, &stdin, |s, f, i| run_source(s, f, i));
        (out, code == 0)
    });

    // ---- runfail: valid programs that fail at RUNTIME: exact expected.txt
    // and a nonzero exit (Always/Requires violations, can-fail misses) ----
    {
        let dir = Path::new(ROOT).join("runfail");
        if dir.is_dir() {
            let mut entries: Vec<PathBuf> = std::fs::read_dir(&dir)
                .unwrap()
                .filter_map(|e| e.ok().map(|e| e.path()))
                .filter(|p| p.is_dir())
                .collect();
            entries.sort();
            for case in entries {
                let input = case.join("input.lykaon");
                let expected = case.join("expected.txt");
                if !input.is_file() || !expected.is_file() {
                    continue;
                }
                let source = read(&input);
                let want = read(&expected).replace('\\', "/").replace("\r\n", "\n");
                let (out, code) = run_roomy(&source, input.to_str().unwrap(), "", |s, f, i| {
                    run_source(s, f, i)
                });
                let out = out.replace('\\', "/").replace("\r\n", "\n");
                let want = want.trim_end_matches('\n');
                let out = out.trim_end_matches('\n');
                if code == 0 {
                    failures.push(format!(
                        "runfail {}: expected runtime failure, but exit was 0:\n{out}",
                        case.display()
                    ));
                } else if out != want {
                    failures.push(format!(
                        "runfail {}: output mismatch.\n--- expected ---\n{:?}\n--- actual ---\n{:?}\n--------------",
                        case.display(),
                        want,
                        out
                    ));
                }
            }
        }
    }

    // ---- test: `lykaon test` output (a failing test still prints its report) ----
    walk_cases("test", &mut failures, |source, name| {
        let (out, _ok) = run_roomy(source, name, "", |s, f, i| test_source(s, f, i));
        (out, true)
    });

    if !failures.is_empty() {
        for f in &failures {
            println!("FAIL: {f}");
        }
        panic!("{} M3 conformance test(s) failed", failures.len());
    }
}

#[test]
fn m3_conformance() {
    run();
}
