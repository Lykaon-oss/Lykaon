//! M2 conformance test runner.
//! Walks tests/conformance/m2 and checks:
//!  - valid/*.lykaon parse cleanly (exit 0, empty output)
//!  - errors/*/input.lykaon produce the exact expected.txt (compile diagnostics)
//!  - run/*/input.lykaon run to the exact expected.txt (optional input.txt = stdin)
//!  - test/*/input.lykaon run `lykaon test` to the exact expected.txt

use lykaon::{check_source, run_source, test_source};
use std::path::{Path, PathBuf};

const ROOT: &str = "tests/conformance/m2";

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
            // Normalize paths in diagnostics so they are location-independent.
            // The compiler may emit absolute paths (canonicalize) or relative
            // paths (from CWD). Try both directory prefixes.
            let mut replacements: Vec<String> = Vec::new();
            // Absolute path from canonicalize (diagnostics may include \\?\ prefix on Windows)
            if let Ok(canon) = std::fs::canonicalize(&input) {
                // Walk up to find the project root directory (named "lykaon")
                let mut base: PathBuf = canon;
                while base
                    .file_name()
                    .map_or(true, |n| n.to_string_lossy().to_lowercase() != "lykaon")
                {
                    match base.parent() {
                        Some(p) if p != base => base = p.to_path_buf(),
                        _ => break,
                    }
                }
                let base_str = base.to_string_lossy().replace('\\', "/");
                replacements.push(base_str.clone());
                replacements.push(format!("\\\\?\\{}", base_str));
            }
            if let Ok(cwd) = std::env::current_dir() {
                if let Ok(rel) = input.strip_prefix(&cwd) {
                    if let Some(dir) = rel.parent() {
                        replacements.push(dir.to_string_lossy().replace('\\', "/"));
                    }
                }
            }
            let mut out = out.replace('\\', "/").replace("\r\n", "\n");
            // Sort by length descending so longest/most specific match wins
            replacements.sort_by(|a, b| b.len().cmp(&a.len()));
            for r in &replacements {
                if !r.is_empty() {
                    let rf = r.replace('\\', "/");
                    if out.contains(&rf) {
                        out = out.replace(&rf, "<root>");
                        break;
                    }
                }
            }
            let want = want.trim_end_matches('\n');
            let out = out.trim_end_matches('\n');
            // Strip caret lines (^^^ under error locations) since their column
            // positions depend on the exact path text which may differ
            let strip_carets = |s: &str| -> String {
                s.lines()
                    .filter(|l| !l.trim().chars().all(|c| c == ' ' || c == '^'))
                    .collect::<Vec<_>>()
                    .join("\n")
            };
            let want = strip_carets(&want);
            let out = strip_carets(&out);
            if ok {
                failures.push(format!(
                    "ERROR {}: expected rejection, but parsed cleanly",
                    case.display()
                ));
            } else if out != want {
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
        let (out, code) = run_source(source, name, &stdin);
        (out, code == 0)
    });

    // ---- run_fail: programs that fail at run time with the exact message ----
    walk_cases("run_fail", &mut failures, |source, name| {
        let stdin = std::fs::read_to_string(Path::new(name).parent().unwrap().join("input.txt"))
            .unwrap_or_default();
        let (out, code) = run_source(source, name, &stdin);
        (out, code != 0)
    });

    // ---- test: `lykaon test` output (a failing test still prints its report) ----
    walk_cases("test", &mut failures, |source, name| {
        let (out, _ok) = test_source(source, name, "");
        (out, true)
    });

    if !failures.is_empty() {
        for f in &failures {
            println!("FAIL: {f}");
        }
        panic!("{} M2 conformance test(s) failed", failures.len());
    }
}

#[test]
fn m2_conformance() {
    run();
}
