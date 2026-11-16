//! Package handling at the tool boundary (ch.6, ch.37): the Lykaon.toml and
//! lykaon.lock parsers and the dependency validation report the book's
//! package errors. These are the integration-side citations of T0505 (no
//! name), T0514 (bad version), T0515 (dependency folder wrong) and T0516
//! (lock file damaged); the fine-grained cases live in src/packages.rs.

use lykaon::packages::{Project, parse_lockfile, parse_project, validate_deps};

/// T0505: a Lykaon.toml without Name is refused.
#[test]
fn packages_project_without_name_is_t0505() {
    let err = parse_project("Version is 1 point 0 point 0.\n").unwrap_err();
    let text = err.to_string();
    assert!(text.contains("T0505"), "expected T0505, got: {text}");
    assert!(
        text.contains("Package has no name"),
        "expected the book's name, got: {text}"
    );
}

/// T0514: a version that is not digits is refused.
#[test]
fn packages_bad_version_is_t0514() {
    let err = parse_project("Name is myapp.\nVersion is one point two.\n").unwrap_err();
    let text = err.to_string();
    assert!(text.contains("T0514"), "expected T0514, got: {text}");
    assert!(
        text.contains("Bad version"),
        "expected the book's name, got: {text}"
    );
}

/// T0515: a Needs folder that is not next to the project is refused before
/// the build.
#[test]
fn packages_missing_dependency_folder_is_t0515() {
    let root = std::env::temp_dir().join(format!("lykaon-pkg-test-{}-t0515", std::process::id()));
    std::fs::create_dir_all(&root).expect("temp root");
    let proj = parse_project(
        "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds helpers from folder helpers.\n",
    )
    .expect("project parses");
    let err = validate_deps(&proj, &root).unwrap_err();
    let text = err.to_string();
    assert!(text.contains("T0515"), "expected T0515, got: {text}");
    assert!(
        text.contains("Dependency folder wrong"),
        "expected the book's name, got: {text}"
    );
    let _ = std::fs::remove_dir_all(&root);
}

/// T0516: a lock line that does not say where the dependency came from is
/// a damaged lock file.
#[test]
fn packages_damaged_lockfile_is_t0516() {
    let err = parse_lockfile("Name is myapp.\nLocked helpers at 1 point 0 point 0.\n").unwrap_err();
    let text = err.to_string();
    assert!(text.contains("T0516"), "expected T0516, got: {text}");
    assert!(
        text.contains("Lock file damaged"),
        "expected the book's name, got: {text}"
    );
}

/// The same manifest parses when it is well formed (the controls above are
/// about the errors, not about the parser refusing good input).
#[test]
fn packages_good_project_and_lock_parse() {
    let proj: Project =
        parse_project("Name is myapp.\nVersion is 1 point 0 point 0.\nEntry is main.lykaon.\n")
            .expect("project parses");
    assert_eq!(proj.name.as_deref(), Some("myapp"));
    assert_eq!(proj.version, Some((1, 0, 0)));
    let lock = parse_lockfile(
        "Name is myapp.\nVersion is 1 point 0 point 0.\nLocked helpers from helpers at 0 point 0 point 0.\nLock allows nothing.\n",
    )
    .expect("lock parses");
    assert_eq!(lock.locked.len(), 1);
}
