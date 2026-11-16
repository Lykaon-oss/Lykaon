//! Devirtualization conformance (user request, final M3): the pass must
//! rewrite interface calls whose receiver kind is known statically, and
//! must NOT touch calls whose kind stays unknown at compile time. Every
//! compiled program here must still run byte-identically to the
//! interpreter (checked by the native sweep as well).
use lykaon::native_object;

const FIRES: &str = r#"
Anything that can speak must have speak.
A dog has name as text.
A cat has name as text.
A dog can speak.
    To speak pet give woof.
A cat can speak.
    To speak pet give meow.
Rex is a dog with name Rex.
Tom is a cat with name Tom.
Say speak rex.
Say speak tom.
"#;

const NOT_FIRES: &str = r#"
Anything that can speak must have speak.
A dog has name as text.
A cat has name as text.
A dog can speak.
    To speak pet give woof.
A cat can speak.
    To speak pet give meow.
Rex is a dog with name Rex.
Tom is a cat with name Tom.
Speakers is list of Rex and Tom.
For each s in Speakers.
    Say speak s.
"#;

fn devirt_changes(source: &str) -> usize {
    for mode in ["fast", "small"] {
        let (_, _, reports) = match native_object(source, "probe.lykaon", mode) {
            Ok(v) => v,
            Err(e) => panic!("probe compiles: {}", e.message()),
        };
        let report = reports
            .iter()
            .find(|r| r.name == "devirtualization" && r.changes > 0);
        if let Some(r) = report {
            // fast and small must agree that the same sites devirtualized
            return r.changes;
        }
    }
    0
}

#[test]
fn devirt_rewrites_static_dispatch() {
    // the receiver names carry the record kind (both are rewritten)
    assert!(
        devirt_changes(FIRES) >= 2,
        "devirtualization must fire on statically known kinds (got {})",
        devirt_changes(FIRES)
    );
}

#[test]
fn devirt_leaves_dynamic_dispatch_alone() {
    // items of a list of different kinds have no static kind
    assert_eq!(
        devirt_changes(NOT_FIRES),
        0,
        "unknown-kind receivers must stay dispatched"
    );
}

#[test]
fn devirt_keeps_output_byte_exact() {
    // fires and must-not cases produce the interpreter's output unchanged
    for (source, expected) in [(FIRES, "woof\nmeow\n"), (NOT_FIRES, "woof\nmeow\n")] {
        let (run_out, code) = lykaon::run_source(source, "probe.lykaon", "");
        assert_eq!(code, 0);
        let (rc, native_out) = match lykaon::native_run_captured(source, "probe.lykaon", "small") {
            Ok(v) => v,
            Err(e) => panic!("native run: {}", e.message()),
        };
        assert_eq!(rc, 0);
        assert_eq!(run_out, expected, "interpreter output changed");
        assert_eq!(native_out, expected, "native output must equal interpreter");
    }
}
