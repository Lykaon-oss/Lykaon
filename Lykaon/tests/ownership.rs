//! Ownership suites (Appendix I section 12, p.241-242).
//! accept/*.lykaon must compile and run cleanly.
//! reject/rNN.lykaon must be rejected, and rNN.err names the expected code.

use lykaon::{check_source, run_source};
use std::path::{Path, PathBuf};

const ACCEPT: &str = "tests/ownership/accept";
const REJECT: &str = "tests/ownership/reject";

fn read(p: &Path) -> String {
    std::fs::read_to_string(p).unwrap_or_else(|e| panic!("cannot read {}: {e}", p.display()))
}

#[test]
fn ownership_suites() {
    let mut failures: Vec<String> = Vec::new();

    // ---- accept: every program compiles and runs cleanly ----
    if Path::new(ACCEPT).is_dir() {
        let mut files: Vec<PathBuf> = std::fs::read_dir(ACCEPT)
            .unwrap()
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().map_or(false, |e| e == "lykaon"))
            .collect();
        files.sort();
        for p in files {
            let source = read(&p);
            let (out, ok) = check_source(&source, p.to_str().unwrap());
            if !ok {
                failures.push(format!(
                    "ACCEPT {}: expected clean compile, got:\n{out}",
                    p.display()
                ));
                continue;
            }
            let (run_out, code) = run_source(&source, p.to_str().unwrap(), "");
            if code != 0 || run_out.contains("Error:") {
                failures.push(format!(
                    "ACCEPT {}: expected clean run, exit={code} output:\n{run_out}",
                    p.display()
                ));
            }
        }
    }

    // ---- reject: every program fails with the code named in its .err file ----
    if Path::new(REJECT).is_dir() {
        let mut files: Vec<PathBuf> = std::fs::read_dir(REJECT)
            .unwrap()
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().map_or(false, |e| e == "lykaon"))
            .collect();
        files.sort();
        for p in files {
            let source = read(&p);
            let err_file = p.with_extension("err");
            if !err_file.is_file() {
                continue;
            }
            let want_code = read(&err_file);
            let want_code = want_code.trim();
            let (out, ok) = check_source(&source, p.to_str().unwrap());
            if ok {
                failures.push(format!(
                    "REJECT {}: expected rejection, but compiled cleanly",
                    p.display()
                ));
            } else if !out.contains(want_code) {
                failures.push(format!(
                    "REJECT {}: expected code {want_code} in the message, got:\n{out}",
                    p.display()
                ));
            }
        }
    }

    if !failures.is_empty() {
        for f in &failures {
            println!("FAIL: {f}");
        }
        panic!("{} ownership suite case(s) failed", failures.len());
    }
}
