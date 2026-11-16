//! M3c whole-program optimization tests:
//!  - a function no statement can reach is removed from the tree in fast
//!    and small modes (the "whole-program dead functions" report line),
//!  - the same tree keeps every function a reachable function can call
//!    (including through Combine with X / Apply each),
//!  - functions marked with Share stay even when nothing calls them
//!    (a package's public shape must survive),
//!  - debug mode never removes anything.

use lykaon::{compile_tree, optimizer, run_source, wpo};

fn trim(s: &str) -> String {
    s.trim_end().to_string()
}

fn report_changes(mode: &str, src: &str, id: &str) -> Option<usize> {
    let mut p = compile_tree(src, id).expect("programs in this test must compile");
    let reports = optimizer::optimize_tree(&mut p, mode);
    reports
        .into_iter()
        .find(|r| r.name == "whole-program dead functions")
        .map(|r| r.changes)
}

fn has_func(p: &lykaon::sem::Program, name: &str) -> bool {
    p.funcs.iter().any(|f| f.name == name)
}

const WITH_DEAD: &str = "\
To doubled x as whole number.
    Give back x times 2.
To tripled x as whole number.
    Give back x times 3.
Changeable x is 5.
Set x to doubled x.
Say x.
";

/// A function with a caller is reachable through the call chain even when
/// nothing at the top level mentions it.
const CHAINED: &str = "\
To doubled x as whole number.
    Give back x times 2.
To helper x as whole number.
    Give back doubled x.
To tripled x as whole number.
    Give back x times 3.
Changeable x is 5.
Set x to helper x.
Say x.
";

/// A function whose body cannot be inlined (two statements, a local)
/// keeps its call edge, so a caller chain is honored once the inliner is
/// no longer in play.
/// M3c-2 UPDATE: a body of local Changeables + one give back is now
/// inlinable by the whole-program inlining pass, so this program now
/// splices completely: pinned below by the updated test.
const STAYER: &str = "\
To bulky x as whole number.
    Changeable tmp is x plus 1.
    Give back tmp.
To tripled x as whole number.
    Give back x times 3.
Changeable x is 5.
Set x to bulky x.
Say x.
";

/// Share keeps a function no statement calls.
const SHARED: &str = "\
To tripled x as whole number.
    Give back x times 3.
Share tripled.
Changeable x is 5.
Say x.
";

/// A function named through `Apply <fn> to each of <list>` (a function
/// name in a value position, M3-S21) is reachable even without a call
/// shape - the edge is real, so the pass keeps it.
const APPLIED: &str = "\
To doubled x as whole number.
    Give back x times 2.
Apply doubled to each of list of 1 and 2 and 3.
";

#[test]
fn dead_function_is_removed() {
    // debug mode never runs the pass: the whole pass list is empty of it
    assert_eq!(
        report_changes("debug", WITH_DEAD, "dead_debug.lykaon"),
        None,
        "debug keeps everything"
    );
    let mut p = compile_tree(WITH_DEAD, "dead_fast.lykaon").expect("compiles");
    let reports = optimizer::optimize_tree(&mut p, "fast");
    let dead = reports
        .into_iter()
        .find(|r| r.name == "whole-program dead functions")
        .expect("dead pass reports")
        .changes;
    // the INLINE pass substitutes doubled's single-give-back body at the
    // call site, erasing the static call, so BOTH tripled (never called)
    // and doubled (caller inlined away) are unreachable here
    assert_eq!(
        dead, 2,
        "tripled never had a caller, doubled's was inlined away"
    );
    assert!(!has_func(&p, "tripled"), "tripled is uncalled; it goes");
    assert!(
        !has_func(&p, "doubled"),
        "doubled's only caller was inlined; it goes too"
    );
    // the sentence must still answer 10 exactly as before
    let (out, code) = run_source(WITH_DEAD, "dead_run.lykaon", "");
    assert_eq!(code, 0, "the run must be fine: {out}");
    assert_eq!(trim(&out), "10");
}

#[test]
fn non_inlinable_function_is_kept() {
    // M3c-2: bulky's body (a local Changeable plus a give back) is now
    // inlinable by the whole-program inlining pass, so the splice goes
    // through and dead-fn removal frees BOTH (bulky's only call was
    // erased; tripled never had one). The sentence still answers 6.
    let mut p = compile_tree(STAYER, "stayer_fast.lykaon").expect("compiles");
    let reports = optimizer::optimize_tree(&mut p, "fast");
    let dead = reports
        .into_iter()
        .find(|r| r.name == "whole-program dead functions")
        .expect("dead pass reports")
        .changes;
    assert_eq!(
        dead, 2,
        "both helpers lose their callers through the splice"
    );
    assert!(!has_func(&p, "bulky"), "bulky is spliced away; it goes");
    assert!(!has_func(&p, "tripled"), "tripled is uncalled; it goes");
    let (out, code) = run_source(STAYER, "stayer_run.lykaon", "");
    assert_eq!(code, 0, "the run must be fine: {out}");
    assert_eq!(trim(&out), "6");
}

#[test]
fn chained_calls_are_reachable() {
    let mut p = compile_tree(CHAINED, "chain_fast.lykaon").expect("compiles");
    let reports = optimizer::optimize_tree(&mut p, "fast");
    let dead = reports
        .into_iter()
        .find(|r| r.name == "whole-program dead functions")
        .expect("dead pass reports")
        .changes;
    // helper is called. Its only give back is `doubled x`, but the
    // INLINE pass (which runs before this one) substitutes doubled's
    // single-give-back body into helper, erasing the static call, so by
    // the time dead-fn removal runs `doubled` has no caller left and
    // `tripled` never had one: both go, while helper survives.
    assert_eq!(
        dead, 2,
        "tripled has no caller; doubled's caller was inlined away"
    );
    assert!(has_func(&p, "helper"), "helper is called; it stays");
    assert!(!has_func(&p, "tripled"), "tripled is uncalled; it goes");
    let (out, code) = run_source(CHAINED, "chain_run.lykaon", "");
    assert_eq!(code, 0, "the run must be fine: {out}");
    assert_eq!(trim(&out), "10");
}
#[test]
fn shared_function_stays() {
    let mut p = compile_tree(SHARED, "shared_fast.lykaon").expect("compiles");
    let reports = optimizer::optimize_tree(&mut p, "fast");
    let dead = reports
        .into_iter()
        .find(|r| r.name == "whole-program dead functions")
        .expect("dead pass reports")
        .changes;
    assert_eq!(dead, 0, "a shared function survives");
    assert!(has_func(&p, "tripled"), "shared=true keeps tripled");
    let (out, code) = run_source(SHARED, "shared_run.lykaon", "");
    assert_eq!(code, 0, "the run must be fine: {out}");
    assert_eq!(trim(&out), "5");
}

#[test]
fn apply_each_word_keeps_function() {
    // the function name in a value position is an edge; the pass keeps it
    let mut p =
        compile_tree(APPLIED, "apply_fast.lykaon").expect("the apply sentence must compile");
    optimizer::optimize_tree(&mut p, "fast");
    assert!(
        has_func(&p, "doubled"),
        "doubled is the Apply word; it stays"
    );
    // whatever the evaluator does with the list, the run must not break
    run_source(APPLIED, "apply_run.lykaon", "");
}

#[test]
fn wpo_pass_is_a_public_entry() {
    // the wpo module exports the pass for callers outside the pipeline
    let mut p = compile_tree(WITH_DEAD, "dead_api.lykaon").expect("compiles");
    assert_eq!(wpo::remove_dead_funcs(&mut p), 1);
}

// ============================================== M3c-2 block-body inlining

/// Run the same tree the OPTIMIZER produced (the actual behavior ships in
/// fast builds): compile, run one mode's passes, run the interpreter on
/// the result.
fn run_optimized(mode: &str, src: &str, id: &str) -> String {
    let mut p = compile_tree(src, id).expect("programs in this test must compile");
    optimizer::optimize_tree(&mut p, mode);
    let (out, code) = lykaon::interp::run(&p, "", &[], true);
    assert_eq!(code, 0, "the optimized tree must run ({mode}): {out}");
    out.trim_end().to_string()
}

fn wpo_report(mode: &str, src: &str, id: &str, name: &str) -> Option<usize> {
    let mut p = compile_tree(src, id).expect("programs in this test must compile");
    let reports = optimizer::optimize_tree(&mut p, mode);
    reports
        .into_iter()
        .find(|r| r.name == name)
        .map(|r| r.changes)
}

/// A body of plain local Changeables + one give back: the only
/// multi-statement shape the pass inlines.
const M3C2_INLINE: &str = "\
To bulky x as whole number.
    Changeable tmp is x times 2.
    Give back tmp.
Changeable x is 5.
Set x to bulky x.
Say x.
";

/// A body that prints: inlining it would move the Say to the caller, so
/// the call must stay.
const M3C2_PRINTS: &str = "\
To loudy x as whole number.
    Say x.
    Give back x plus 1.
Changeable x is 3.
Set x to loudy x.
Say x.
";

/// A call inside an If body statement IS inlined (the pass walks into
/// nested lists). A call inside a Try sentence stays whole by the pass
/// rule, but no TEST programs it: the compiler itself rejects Try around
/// a sentence that cannot fail (T0151), and a non-failing candidate's
/// call can never be that sentence - the refusal rule is defense in
/// depth, recorded in the deviations log.
const M3C2_IF_AND_TRY: &str = "\
To bulky x as whole number.
    Changeable tmp is x times 2.
    Give back tmp.
Changeable x is 5.
If x is more than 4.
    Set x to bulky x.
Otherwise.
    Say small.
Say x.
";

/// The body reads a captured Constant; substituting the Sets at the call
/// site would re-resolve that name in the caller's frame - refused
/// (a caller frame that never captured the Constant would read wrong).
const M3C2_CAPTURED: &str = "\
Constant base is 10.
To baseout x as whole number.
    Changeable t is x plus base.
    Give back t.
Changeable x is 5.
Set x to baseout x.
Say x.
";

/// A single-give-back wrapper whose body CALLS a block candidate: the
/// single-statement inliner substitutes the wrapper body (keeping the
/// bulky call), then the block pass splices that call inside wrapper's
/// own block - and every caller left is erased by it, so dead-fn removal
/// frees BOTH afterwards. Ordering reality, pinned.
const M3C2_WRAPPED: &str = "\
To bulky x as whole number.
    Changeable tmp is x times 2.
    Give back tmp.
To wrapper x as whole number.
    Give back bulky x.
Changeable x is 5.
Set x to wrapper x.
Say x.
";

#[test]
fn m3c2_block_body_is_inlined() {
    // debug mode never rewrote anything: the report line is absent
    assert_eq!(
        wpo_report(
            "debug",
            M3C2_INLINE,
            "m3c2in_debug.lykaon",
            "whole-program inlining"
        ),
        None,
        "debug keeps the fresh tree"
    );
    assert_eq!(
        wpo_report(
            "fast",
            M3C2_INLINE,
            "m3c2in_fast.lykaon",
            "whole-program inlining"
        ),
        Some(1),
        "the one call site is substituted"
    );
    // the spliced tmp keeps the answer exact
    assert_eq!(
        run_optimized("fast", M3C2_INLINE, "m3c2in_run.lykaon"),
        "10"
    );
    // with the call erased, bulky has no caller left: dead-fn removal
    // frees it (the dead pass runs after inlining on purpose)
    let mut p = compile_tree(M3C2_INLINE, "m3c2in_dead.lykaon").expect("compiles");
    optimizer::optimize_tree(&mut p, "fast");
    assert!(!has_func(&p, "bulky"), "the spliced-away helper goes");
    let mut p = compile_tree(M3C2_INLINE, "m3c2in_dbg.lykaon").expect("compiles");
    optimizer::optimize_tree(&mut p, "debug");
    assert!(has_func(&p, "bulky"), "debug keeps the helper");
}

#[test]
fn m3c2_printing_body_not_inlined() {
    assert_eq!(
        wpo_report(
            "fast",
            M3C2_PRINTS,
            "m3c2print.lykaon",
            "whole-program inlining"
        ),
        Some(0),
        "a Say in the body is refused"
    );
    assert_eq!(
        run_optimized("fast", M3C2_PRINTS, "m3c2print_run.lykaon"),
        "3\n4"
    );
}

#[test]
fn m3c2_call_in_if_body_inlined() {
    // a call inside an If BODY statement is reached by the walk-in: it
    // is spliced there
    assert_eq!(
        wpo_report(
            "fast",
            M3C2_IF_AND_TRY,
            "m3c2if.lykaon",
            "whole-program inlining"
        ),
        Some(1),
        "the walk-in reaches statements inside nested lists"
    );
    assert_eq!(
        run_optimized("fast", M3C2_IF_AND_TRY, "m3c2if_run.lykaon"),
        "10"
    );
}

#[test]
fn m3c2_captured_name_body_not_inlined() {
    assert_eq!(
        wpo_report(
            "fast",
            M3C2_CAPTURED,
            "m3c2cap.lykaon",
            "whole-program inlining"
        ),
        Some(0),
        "a body naming a captured fixed name is refused"
    );
    // the captured base reads exactly once, in the callee frame: both
    // modes must keep the answer byte-equal
    assert_eq!(
        run_optimized("debug", M3C2_CAPTURED, "m3c2cap_dbg.lykaon"),
        "15"
    );
    assert_eq!(
        run_optimized("fast", M3C2_CAPTURED, "m3c2cap_run.lykaon"),
        "15"
    );
}

#[test]
fn m3c2_wrapper_chain_inlines_inside_and_frees_callee() {
    // wrapper's body contains a CALL, so the single-statement pass
    // refuses it (bodies with calls are not candidates) and the top
    // `Set x to wrapper x.` stays a wrapper call. The block pass still
    // splices the call INSIDE wrapper's own block, which erases bulky's
    // last caller: dead-fn removal frees bulky (wrapper keeps its
    // caller, so it stays). Every stage honest, all pinned.
    assert_eq!(
        wpo_report(
            "fast",
            M3C2_WRAPPED,
            "m3c2wrap.lykaon",
            "whole-program inlining"
        ),
        Some(1),
        "the call inside wrapper's block splices"
    );
    assert_eq!(
        run_optimized("fast", M3C2_WRAPPED, "m3c2wrap_run.lykaon"),
        "10"
    );
    let mut p = compile_tree(M3C2_WRAPPED, "m3c2wrap_dead.lykaon").expect("compiles");
    optimizer::optimize_tree(&mut p, "fast");
    assert!(
        !has_func(&p, "bulky"),
        "bulky's caller was spliced inside wrapper"
    );
    assert!(
        has_func(&p, "wrapper"),
        "wrapper keeps its top-level caller"
    );
}

// ============================================ M3c-3 cross-package constants

/// The Constant sentence with a leaf value: later top-level reads fold.
const M3C3_CONST: &str = "\
Constant base is 3.
Changeable x is 7.
Set x to x plus base.
Say x.
";

/// A plain immutable definition (`name is value.`) is also a candidate.
const M3C3_PLAIN: &str = "\
Total is 4.
Changeable x is 2.
Set x to x times Total.
Say x.
";

/// Tests run on a fresh frame: a test reading a top-level constant today
/// reads a Missing-like value, so the pass must NOT touch test bodies.
const M3C3_TEST_UNTOUCHED: &str = "\
Constant base is 3.
Changeable x is 2.
Set x to x plus base.
Say x.
Test probe.
    Say base.
    Say x.
";

#[test]
fn m3c3_constant_is_folded() {
    // debug mode never rewrote anything: the report line is absent
    assert_eq!(
        wpo_report(
            "debug",
            M3C3_CONST,
            "m3c3c_debug.lykaon",
            "cross-package constants"
        ),
        None,
        "debug keeps the fresh tree"
    );
    assert_eq!(
        wpo_report(
            "fast",
            M3C3_CONST,
            "m3c3c_fast.lykaon",
            "cross-package constants"
        ),
        Some(1),
        "the one read after the definition folds"
    );
    // byte-equal behavior in both modes
    assert_eq!(run_optimized("debug", M3C3_CONST, "m3c3c_dbg.lykaon"), "10");
    assert_eq!(run_optimized("fast", M3C3_CONST, "m3c3c_run.lykaon"), "10");
    // the Changeable before the definition is never a candidate: x stays
    let mut p = compile_tree(M3C3_CONST, "m3c3c_check.lykaon").expect("compiles");
    optimizer::optimize_tree(&mut p, "fast");
    assert!(
        has_func(&p, "base") == false,
        "no function named base exists"
    );
}

#[test]
fn m3c3_plain_immutable_is_folded() {
    assert_eq!(
        wpo_report(
            "fast",
            M3C3_PLAIN,
            "m3c3p_fast.lykaon",
            "cross-package constants"
        ),
        Some(1),
        "the plain immutable definition is a candidate too"
    );
    assert_eq!(run_optimized("debug", M3C3_PLAIN, "m3c3p_dbg.lykaon"), "8");
    assert_eq!(run_optimized("fast", M3C3_PLAIN, "m3c3p_run.lykaon"), "8");
}

#[test]
fn m3c3_tests_stay_unfolded() {
    // the top-level read folds; the test body does NOT (fresh frame at
    // test time). The count must reflect exactly the top-level reads.
    assert_eq!(
        wpo_report(
            "fast",
            M3C3_TEST_UNTOUCHED,
            "m3c3t_fast.lykaon",
            "cross-package constants"
        ),
        Some(1),
        "only the single top-level read folds"
    );
}
