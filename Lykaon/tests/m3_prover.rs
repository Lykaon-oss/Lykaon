//! M3b contract-prover tests:
//!  - a contraction PROVEN always true is skipped at run time (fires test:
//!    the halve sample still answers correctly and the prover reports it),
//!  - a disproven contract is NOT skipped: the run-time check stays and
//!    fails the program with the exact T0602 wording,
//!  - proofs survive multi-path give backs (If / Otherwise),
//!  - `Lykaon_NO_PROVER=1` (child process — the off switch is a OnceLock)
//!    restores full checking without changing valid runs.

use lykaon::{compile_tree, prover, run_source};
use std::process::Command;

fn trim(s: &str) -> String {
    s.trim_end().to_string()
}

/// The conformance halve sample: the Ensures IS provable (n > 0 gives
/// n divided by 2 > 0), so it is skipped; the sentence still works.
const HALVE: &str = "\
To halve n.
    Requires n is more than 0.
    Ensures result is more than 0.
    Give back n divided by 2.
Say halve 8.
";

#[test]
fn proven_contract_skips_and_runs() {
    let (out, code) = run_source(HALVE, "halve.lykaon", "");
    assert_eq!(code, 0, "halve must run fine: {out}");
    assert_eq!(trim(&out), "4.00", "halve output");
    // and the prover actually proved it (bookkeeping for `lykaon build`)
    let prog = compile_tree(HALVE, "halve.lykaon").expect("compiles");
    assert_eq!(
        prover::proof_counts(&prog),
        1,
        "exactly the one Ensures is proven"
    );
}

/// M4 user request (2026-11-08): the six mainline benchmarks remove zero
/// checks because they state no contracts. tests/bench/contracts.lykaon is
/// the proof artifact where the removal IS counted: `lykaon install`-style
/// build report and `lykaon bench` print checks_removed=1 for it, off-flag
/// child runs stay byte-identical, and the count is exactly the proven
/// Ensures (the Requires never gets skipped by design).
const CONTRACTS_ARTIFACT_PATH: &str = "tests/bench/contracts.lykaon";

#[test]
fn prover_removes_checks_in_the_artifact_program() {
    let source = std::fs::read_to_string(CONTRACTS_ARTIFACT_PATH)
        .expect("the artifact program must exist next to the tests");
    // the run is green in every mode (the proven Ensures is skipped, the
    // live Requires holds for every call site the program makes)
    let (out, code) = run_source(&source, "contracts_artifact.lykaon", "");
    assert_eq!(code, 0, "the artifact run must be fine: {out}");
    assert_eq!(trim(&out), "4.00\n5.00\n2.00", "artifact output");
    // the compile report counts exactly the one proven Ensures as removed
    let mut p = compile_tree(&source, CONTRACTS_ARTIFACT_PATH).expect("compiles");
    assert_eq!(
        prover::checks_removed(&mut p),
        1,
        "exactly the one Ensures check is removed and reported"
    );
}

/// A DISPROVEN contract: n is less than 10, so n divided by 2 is at most
/// barely 5 — far below 100. The prover must NOT skip this check; leaving
/// it live makes the sentence fail with the exact run-time wording.
const SHRINK: &str = "\
To shrink n.
    Requires n is less than 10.
    Ensures result is more than 100.
    Give back n divided by 2.
Say shrink 5.
";

#[test]
fn disproven_contract_keeps_check_and_fails() {
    let (out, code) = run_source(SHRINK, "shrink.lykaon", "");
    assert_ne!(code, 0, "the live Ensures must fail the program: {out}");
    let want = "Error: Ensures failed: Ensures result is more than 100 (T0602)\n\
                Fix: The ensures condition 'Ensures result is more than 100' is not met.";
    assert_eq!(trim(&out), want);
    // nothing proven here: the check stays in every mode
    let prog = compile_tree(SHRINK, "shrink.lykaon").expect("compiles");
    assert_eq!(prover::proof_counts(&prog), 0, "disproven checks are kept");
}

/// Both branches' give backs flow into one result range: Requires n at
/// least 1, either branch answers at least 1 — proven with no checking.
const CLAMP: &str = "\
To clamp n.
    Requires n is at least 1.
    Ensures result is at least 1.
    If n is more than 10.
        Give back n.
    Otherwise.
        Give back 1.
Say clamp 3.
Say clamp 40.
";

#[test]
fn multipath_give_backs_join() {
    let (out, code) = run_source(CLAMP, "clamp.lykaon", "");
    assert_eq!(code, 0, "clamp must run fine: {out}");
    assert_eq!(trim(&out), "1\n40", "clamp outputs both branches");
    let prog = compile_tree(CLAMP, "clamp.lykaon").expect("compiles");
    assert_eq!(prover::proof_counts(&prog), 1, "branch join proves it");
}

/// The off switch (child process, because the flag is read once): with
/// `Lykaon_NO_PROVER=1` every check runs again — valid sentences still pass.
#[test]
fn off_switch_restores_checks() {
    let tmp = std::env::temp_dir().join("lykaon_m3b_prover_off.lykaon");
    std::fs::write(&tmp, HALVE).expect("write temp source");
    let out = Command::new(env!("CARGO_BIN_EXE_lykaonc-cli"))
        .arg("run")
        .arg(&tmp)
        .env("Lykaon_NO_PROVER", "1")
        .output()
        .expect("spawn lykaonc.exe");
    assert!(out.status.success(), "no-prover run must still pass");
    assert_eq!(
        String::from_utf8_lossy(&out.stdout).trim_end(),
        "4.00",
        "same answer with the prover off"
    );
    std::fs::remove_file(&tmp).ok();
}

/// M3b-3 per-site Always: a construction whose parts are statically good
/// AND a Set part write with a statically good value both skip their site
/// check; the sentence runs and the counter proves the skips happen.
const AGE_SITE: &str = "\
A person has name as text and age as whole number.
    Always age of value is at least 0.
Changeable maya is a person with name Maya and age 5.
Set age of maya to 3.
Say age of maya.
";

#[test]
fn always_site_skips_proven_sites() {
    let (out, code) = run_source(AGE_SITE, "agesite.lykaon", "");
    assert_eq!(code, 0, "the good site must run fine: {out}");
    assert_eq!(trim(&out), "3", "the part write took hold");
    let mut prog = compile_tree(AGE_SITE, "agesite.lykaon").expect("compiles");
    assert_eq!(
        prover::site_counts(&mut prog),
        2,
        "construction + Set part both proven"
    );
}

/// M3b-3 must-not: a Set part write whose value is DISPROVEN keeps its
/// live site check and fails at run time with the exact wording.
const AGE_SITE_BAD: &str = "\
A person has name as text and age as whole number.
    Always age of value is at least 0.
Changeable maya is a person with name Maya and age 5.
Set age of maya to 0 minus 5.
Say age of maya.
";

#[test]
fn always_site_disproven_keeps_check() {
    let (out, code) = run_source(AGE_SITE_BAD, "agesite_bad.lykaon", "");
    assert_ne!(code, 0, "the bad part write must fail: {out}");
    let want = "Error: Always failed: age of value is at least 0. (T0602)\n\
                Fix: The kind's Always line does not allow this value.";
    assert_eq!(trim(&out), want);
    let mut prog = compile_tree(AGE_SITE_BAD, "agesite_bad.lykaon").expect("compiles");
    // only the construction site is proven; the bad write keeps checking
    assert_eq!(
        prover::site_counts(&mut prog),
        1,
        "the bad write is not skipped"
    );
}
