//! M1a conformance test runner.
//! Walks tests/conformance/m1a and checks:
//!  - valid/*.lykaon parse cleanly (exit 0, empty output)
//!  - errors/*/input.lykaon produce the exact expected.txt
//!  - fmt/*.lykaon format to expected.lykaon

use lykaon::{check_bytes, check_source, format_source};
use std::path::{Path, PathBuf};

const ROOT: &str = "tests/conformance/m1a";

fn read(p: &Path) -> String {
    std::fs::read_to_string(p).unwrap_or_else(|e| panic!("cannot read {}: {e}", p.display()))
}

fn run() {
    let root = Path::new(ROOT);
    let mut failures: Vec<String> = Vec::new();

    // ---- valid ----
    let valid = root.join("valid");
    if valid.is_dir() {
        for entry in std::fs::read_dir(&valid).unwrap() {
            let entry = entry.unwrap();
            let p = entry.path();
            if p.extension().map_or(false, |e| e == "lykaon") {
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
    }

    // ---- errors ----
    let errors = root.join("errors");
    if errors.is_dir() {
        for entry in std::fs::read_dir(&errors).unwrap() {
            let entry = entry.unwrap();
            let dir = entry.path();
            if !dir.is_dir() {
                continue;
            }
            let input = dir.join("input.lykaon");
            let expected = dir.join("expected.txt");
            if !input.is_file() || !expected.is_file() {
                continue;
            }
            let source = read(&input);
            let want = read(&expected);
            // Normalize path separators for cross-platform comparison.
            let want = want.replace('\\', "/");
            let (out, ok) = check_source(&source, input.to_str().unwrap());
            let out = out.replace('\\', "/");
            if ok {
                failures.push(format!(
                    "ERROR {}: expected rejection, but parsed cleanly",
                    dir.display()
                ));
            } else if out != want {
                failures.push(format!(
                    "ERROR {}: output mismatch.\n--- expected ---\n{:?}\n--- actual ---\n{:?}\n--------------",
                    dir.display(),
                    want,
                    out
                ));
            }
        }
    }

    // ---- warn: warnings print with ok=true (the exact output) ----
    let warn = root.join("warn");
    if warn.is_dir() {
        for entry in std::fs::read_dir(&warn).unwrap() {
            let entry = entry.unwrap();
            let p = entry.path();
            if p.extension().map_or(false, |e| e == "lykaon") {
                let expected = p.with_extension("expected.txt");
                if !expected.is_file() {
                    continue;
                }
                let source = read(&p);
                let want = read(&expected);
                let want = want.replace('\\', "/");
                let (out, ok) = check_source(&source, p.to_str().unwrap());
                let out = out.replace('\\', "/");
                if !ok {
                    failures.push(format!(
                        "WARN {}: expected a warning, but the program was rejected:\n{out}",
                        p.display()
                    ));
                } else if out != want {
                    failures.push(format!(
                        "WARN {}: output mismatch.\n--- expected ---\n{:?}\n--- actual ---\n{:?}\n--------------",
                        p.display(),
                        want,
                        out
                    ));
                }
            }
        }
    }

    // ---- fmt ----
    let fmt = root.join("fmt");
    if fmt.is_dir() {
        for entry in std::fs::read_dir(&fmt).unwrap() {
            let entry = entry.unwrap();
            let p = entry.path();
            if p.extension().map_or(false, |e| e == "lykaon") {
                let stem = p.file_stem().unwrap().to_str().unwrap();
                let expected = p.with_extension("expected.lykaon");
                if !expected.is_file() {
                    continue;
                }
                let source = read(&p);
                let want = read(&expected);
                let got = format_source(&source);
                if got != want {
                    failures.push(format!(
                        "FMT {}: output mismatch.\n--- expected ---\n{:?}\n--- actual ---\n{:?}\n--------------",
                        p.display(),
                        want,
                        got
                    ));
                }
            }
        }
    }

    if !failures.is_empty() {
        for f in &failures {
            println!("FAIL: {f}");
        }
        panic!("{} M1a conformance test(s) failed", failures.len());
    }
}

#[test]
fn m1a_conformance() {
    run();
}

/// T0018: a file that is not UTF-8 is refused by the byte-level check with
/// the book's wording (the text-level API cannot see such bytes).
#[test]
fn m1a_file_not_utf8_is_t0018() {
    let bytes = b"Say hi.\nSay \xff\xfe goodbye.\n";
    let (out, ok) = check_bytes(bytes, "bad.lykaon");
    assert!(!ok, "expected a rejection, got: {out}");
    assert!(out.contains("T0018"), "expected T0018, got: {out}");
    assert!(
        out.contains("The file holds bytes that are not valid UTF-8."),
        "expected the book's cause, got: {out}"
    );
    assert!(
        out.contains("Save the file as UTF-8."),
        "expected the book's fix, got: {out}"
    );
    // a BOM is not a failure: the same check passes a UTF-8 file with one
    let (out, ok) = check_bytes(b"\xef\xbb\xbfSay hi.\n", "bom.lykaon");
    assert!(ok, "expected the BOM to be ignored, got: {out}");
}
