//! M1b conformance test runner.
//! Walks tests/conformance/m1b and checks:
//!  - valid/<name>/input.lykaon: `lykaon run` output matches expected.txt
//!  - errors/<name>/input.lykaon: `lykaon check` output matches expected.txt

use lykaon::{check_source, run_source};
use std::path::{Path, PathBuf};

const ROOT: &str = "tests/conformance/m1b";

fn read(p: &Path) -> String {
    std::fs::read_to_string(p).unwrap_or_else(|e| panic!("cannot read {}: {e}", p.display()))
}

fn pairs(dir: &Path) -> Vec<(PathBuf, PathBuf)> {
    let mut out = Vec::new();
    if dir.is_dir() {
        for entry in std::fs::read_dir(dir).unwrap() {
            let sub = entry.unwrap().path();
            if !sub.is_dir() {
                continue;
            }
            let input = sub.join("input.lykaon");
            let expected = sub.join("expected.txt");
            if input.is_file() && expected.is_file() {
                out.push((input, expected));
            }
        }
    }
    out.sort();
    out
}

fn run() {
    let root = Path::new(ROOT);
    let mut failures: Vec<String> = Vec::new();

    // ---- valid: run ----
    for (input, expected) in pairs(&root.join("valid")) {
        let source = read(&input);
        let want = read(&expected).replace('\\', "/");
        // the greeter (Ch.71) reads the reply Maya; other tests leave stdin empty
        let stdin_text = if input.to_string_lossy().contains("ch71_greeter") {
            "Maya\n"
        } else {
            ""
        };
        let (out, _code) = run_source(&source, input.to_str().unwrap(), stdin_text);
        let out = out.replace('\\', "/");
        if out != want {
            failures.push(format!(
                "RUN {}: output mismatch.\n--- expected ---\n{:?}\n--- actual ---\n{:?}\n--------------",
                input.display(),
                want,
                out
            ));
        }
    }

    // ---- errors: check ----
    for (input, expected) in pairs(&root.join("errors")) {
        let source = read(&input);
        let want = read(&expected).replace('\\', "/");
        let (out, ok) = check_source(&source, input.to_str().unwrap());
        let out = out.replace('\\', "/");
        if ok {
            failures.push(format!(
                "ERROR {}: expected rejection, but parsed cleanly",
                input.display()
            ));
        } else if out != want {
            failures.push(format!(
                "ERROR {}: output mismatch.\n--- expected ---\n{:?}\n--- actual ---\n{:?}\n--------------",
                input.display(),
                want,
                out
            ));
        }
    }

    if !failures.is_empty() {
        for f in &failures {
            println!("FAIL: {f}");
        }
        panic!("{} M1b conformance test(s) failed", failures.len());
    }
}

#[test]
fn m1b_conformance() {
    run();
}
