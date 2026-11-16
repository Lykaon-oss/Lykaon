//! Package handling: Lykaon.toml / lykaon.lock, local-folder dependencies,
//! git dependencies (M4-G84), `lykaon add / remove / update` (ch.6, M3-D8 /
//! M3-D9 / section 6, M4-11).
//!
//! Lykaon.toml (project configuration):
//!   Name is <name>.
//!   Version is <major> point <minor> point <patch>.
//!   Entry is <file>.lykaon.
//!   Needs <name1> and <name2> from folder <folder>.
//!   Needs <name> from git <address>.
//!   Needs <name> from git <address> at version <major> point <minor> point <patch>.
//!
//! lykaon.lock (lockfile, written by `lykaon update`):
//!   Name is <name>.
//!   Version is <major> point <minor> point <patch>.
//!   Locked <name1> from <folder1> at <version>.
//!   Locked <name2> from git <address2> at <version>.
//!   Lock allows nothing.

use std::path::{Path, PathBuf};

/// Where a dependency comes from.
#[derive(Clone, Debug, PartialEq)]
pub enum Source {
    /// A folder next to the project (M3-D8).
    Folder(PathBuf),
    /// A git address, optionally pinned to a version tag (M4-G84).
    Git {
        url: String,
        version: Option<(u64, u64, u64)>,
    },
}

/// One dependency of the project.
#[derive(Clone, Debug, PartialEq)]
pub struct Dependency {
    pub name: String,
    pub source: Source,
}

/// A parsed Lykaon.toml project file.
#[derive(Clone, Debug, Default)]
pub struct Project {
    pub name: Option<String>,
    pub version: Option<(u64, u64, u64)>,
    pub entry: Option<String>,
    pub needs: Vec<Dependency>,
}

/// A parsed lykaon.lock file.
#[derive(Clone, Debug, Default)]
pub struct Lockfile {
    pub name: Option<String>,
    pub version: Option<(u64, u64, u64)>,
    pub locked: Vec<LockedDep>,
}

/// One locked dependency: where it came from, at which version, and (for a
/// git source) the content checksum the lock holds it to.
#[derive(Clone, Debug, PartialEq)]
pub struct LockedDep {
    pub name: String,
    pub source: Source,
    pub version: (u64, u64, u64),
    pub checksum: Option<String>,
}

/// Error reading or validating a project / lock file.
#[derive(Clone, Debug)]
pub enum PackageError {
    T0505 { what: String }, // package has no name
    T0514 { what: String }, // bad version
    T0515 { what: String }, // dependency folder wrong
    T0516 { what: String }, // lock file damaged
    T0520 { what: String }, // git dependency failed (M4-T0520)
    Io { what: String },
}

impl std::fmt::Display for PackageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PackageError::T0505 { what } => write!(f, "T0505: Package has no name: {what}"),
            PackageError::T0514 { what } => write!(f, "T0514: Bad version: {what}"),
            PackageError::T0515 { what } => write!(f, "T0515: Dependency folder wrong: {what}"),
            PackageError::T0516 { what } => write!(f, "T0516: Lock file damaged: {what}"),
            // the book wording: "Git dependency failed" / "A Git address
            // cannot be fetched..." / Fix: "Check the address and run
            // lykaon update."
            PackageError::T0520 { what } => {
                write!(
                    f,
                    "T0520: Git dependency failed: {what}\nCheck the address and run lykaon update."
                )
            }
            PackageError::Io { what } => write!(f, "I/O error: {what}"),
        }
    }
}

/// Parse an Lykaon.toml file.
pub fn parse_project(text: &str) -> Result<Project, PackageError> {
    let mut proj = Project::default();
    for raw in text.lines() {
        let t = raw.trim();
        let low = t.to_ascii_lowercase();
        if low.starts_with("name is ") && low.ends_with('.') {
            let name = t[8..t.len() - 1].trim();
            if !name.is_empty() {
                proj.name = Some(name.to_string());
            }
        } else if low.starts_with("version is ") && low.ends_with('.') {
            let rest = &t[11..t.len() - 1];
            proj.version = Some(parse_version(rest)?);
        } else if low.starts_with("entry is ") && low.ends_with('.') {
            let entry = t[9..t.len() - 1].trim();
            if !entry.is_empty() {
                proj.entry = Some(entry.to_string());
            }
        } else if low.starts_with("needs ") && low.ends_with('.') && low.contains(" from git") {
            // Needs <name> [and <name>] from git <address> [at version V]. (M4-G84)
            // the padded search also reads the nameless form, whose body
            // starts with `from git` itself
            let body = &t[6..t.len() - 1];
            let padded = format!(" {body}");
            let low_pad = padded.to_ascii_lowercase();
            let Some(git_pos) = low_pad.find(" from git") else {
                continue;
            };
            let names_part = padded[..git_pos].trim();
            let rest = padded[git_pos + 9..].trim();
            // optional " at version <three numbers joined by point>"
            let (address, version) = match rest.to_ascii_lowercase().rfind(" at version ") {
                Some(at) => {
                    let url = rest[..at].trim();
                    let v = parse_version(rest[at + 12..].trim())?;
                    (url.to_string(), Some(v))
                }
                None => (rest.to_string(), None),
            };
            if address.is_empty() {
                return Err(PackageError::T0520 {
                    what: "the Needs line has no git address".to_string(),
                });
            }
            let mut names: Vec<String> = names_part
                .split_whitespace()
                .filter(|w| !w.eq_ignore_ascii_case("and"))
                .map(|w| w.to_string())
                .collect();
            if names.is_empty() {
                // the dependency name defaults to the address's last part
                let stem = address
                    .trim_end_matches('/')
                    .rsplit('/')
                    .next()
                    .unwrap_or(&address)
                    .trim_end_matches(".git");
                names.push(stem.to_string());
            }
            for name in names {
                proj.needs.push(Dependency {
                    name,
                    source: Source::Git {
                        url: address.clone(),
                        version,
                    },
                });
            }
        } else if low.starts_with("needs ") && low.ends_with('.') && low.contains(" from folder ") {
            // Needs <name> [and <name>] from folder <folder>.
            let body = &t[6..t.len() - 1];
            let lowb = body.to_ascii_lowercase();
            let Some(from_pos) = lowb.find(" from folder ") else {
                continue;
            };
            let names_part = body[..from_pos].trim();
            let folder = body[from_pos + 13..].trim();
            let mut names: Vec<String> = names_part
                .split_whitespace()
                .filter(|w| !w.eq_ignore_ascii_case("and"))
                .map(|w| w.to_string())
                .collect();
            if names.is_empty() {
                names.push(folder.to_string());
            }
            let folder_path = PathBuf::from(folder);
            for name in names {
                proj.needs.push(Dependency {
                    name,
                    source: Source::Folder(folder_path.clone()),
                });
            }
        }
    }
    if proj.name.is_none() {
        return Err(PackageError::T0505 {
            what: "Lykaon.toml lacks Name is ....".to_string(),
        });
    }
    if proj.version.is_none() {
        return Err(PackageError::T0514 {
            what: "Lykaon.toml lacks Version is ....".to_string(),
        });
    }
    Ok(proj)
}

/// Parse a version string "1 point 2 point 3".
fn parse_version(rest: &str) -> Result<(u64, u64, u64), PackageError> {
    let low = rest.to_ascii_lowercase();
    let parts: Vec<&str> = low.split_whitespace().filter(|w| *w != "point").collect();
    if parts.len() != 3 {
        return Err(PackageError::T0514 {
            what: format!("Version is not three numbers joined by point: {rest}"),
        });
    }
    let mut nums = Vec::new();
    for p in parts {
        match p.parse::<u64>() {
            Ok(n) => nums.push(n),
            Err(_) => {
                return Err(PackageError::T0514 {
                    what: format!("Version is not three numbers joined by point: {rest}"),
                });
            }
        }
    }
    Ok((nums[0], nums[1], nums[2]))
}

/// Parse an lykaon.lock file.
pub fn parse_lockfile(text: &str) -> Result<Lockfile, PackageError> {
    let mut lock = Lockfile::default();
    for raw in text.lines() {
        let t = raw.trim();
        let low = t.to_ascii_lowercase();
        if low.starts_with("name is ") && low.ends_with('.') {
            lock.name = Some(t[8..t.len() - 1].trim().to_string());
        } else if low.starts_with("version is ") && low.ends_with('.') {
            lock.version = Some(parse_version(&t[11..t.len() - 1])?);
        } else if low.starts_with("locked ") && low.ends_with('.') {
            // Locked <name> from <folder> at <version>.
            // Locked <name> from git <address> at <version>. (M4-11)
            // Locked <name> from git <address> at <version> with checksum HEX.
            let rest = &t[7..t.len() - 1];
            let lowr = rest.to_ascii_lowercase();
            let Some(at_pos) = lowr.rfind(" at ") else {
                return Err(PackageError::T0516 {
                    what: format!("Bad locked line: {rest}"),
                });
            };
            let name_folder = rest[..at_pos].trim();
            let mut ver_str = rest[at_pos + 4..].trim();
            let mut checksum = None;
            if let Some(ck) = ver_str.to_ascii_lowercase().rfind(" with checksum ") {
                checksum = Some(ver_str[ck + 15..].trim().to_string());
                ver_str = ver_str[..ck].trim();
            }
            let version = parse_version(ver_str)?;
            let Some(from_pos) = name_folder.to_ascii_lowercase().rfind(" from ") else {
                return Err(PackageError::T0516 {
                    what: format!("Bad locked line: {rest}"),
                });
            };
            let name = name_folder[..from_pos].trim().to_string();
            let source_part = name_folder[from_pos + 6..].trim();
            let low_src = source_part.to_ascii_lowercase();
            let source = if low_src == "git" || low_src.starts_with("git ") {
                Source::Git {
                    url: source_part[3..].trim().to_string(),
                    version: Some(version),
                }
            } else {
                Source::Folder(PathBuf::from(source_part))
            };
            lock.locked.push(LockedDep {
                name,
                source,
                version,
                checksum,
            });
        }
    }
    Ok(lock)
}

/// Validate that every dependency can be used: a folder dependency exists
/// relative to `root`; a git dependency has its cache clone in place (run
/// `lykaon update` first, per the T0520 fix wording).
pub fn validate_deps(proj: &Project, root: &Path) -> Result<(), PackageError> {
    for dep in &proj.needs {
        match &dep.source {
            Source::Folder(folder) => {
                let full = root.join(folder);
                if !full.is_dir() {
                    return Err(PackageError::T0515 {
                        what: format!(
                            "Dependency {} folder {} does not exist",
                            dep.name,
                            folder.display()
                        ),
                    });
                }
                let _toml = full.join("Lykaon.toml");
                // The Lykaon.toml inside the dependency is checked when it is built.
            }
            Source::Git { .. } => {
                let cache = git_cache_dir(root, &dep.name);
                if !cache.is_dir() {
                    return Err(PackageError::T0520 {
                        what: format!(
                            "dependency {} is not fetched yet. Run lykaon update.",
                            dep.name
                        ),
                    });
                }
            }
        }
    }
    Ok(())
}

/// Where a git dependency's clone lives, relative to the project root.
pub fn git_cache_dir(root: &Path, name: &str) -> PathBuf {
    root.join(".lykaon-cache").join(name)
}

/// Fetch every git dependency into its cache folder (M4-11): `git clone`
/// when the cache is empty, `git fetch` when it exists (so `lykaon update`
/// advances an unpinned dependency and sees a rewritten tag), then
/// `git checkout` of the pinned version tag when the manifest pins one.
/// A missing git tool, a bad address or a missing tag is T0520 (the book's
/// "Git dependency failed"). The returned (name, checksum) pairs go into
/// the lock; a checksum that differs from the lock for the SAME version is
/// T0520 ("its checksum differs").
pub fn sync_git_deps(
    proj: &Project,
    root: &Path,
    lock: Option<&Lockfile>,
) -> Result<Vec<(String, String)>, PackageError> {
    let mut fetched = Vec::new();
    for dep in &proj.needs {
        let Source::Git { url, version } = &dep.source else {
            continue;
        };
        let cache = git_cache_dir(root, &dep.name);
        if !cache.is_dir() {
            let run = std::process::Command::new("git")
                .arg("clone")
                .arg("--quiet")
                .arg(url)
                .arg(&cache)
                .output();
            let out = match run {
                Ok(o) => o,
                Err(e) => {
                    return Err(PackageError::T0520 {
                        what: format!("cannot run git: {e}"),
                    });
                }
            };
            if !out.status.success() {
                return Err(PackageError::T0520 {
                    what: format!(
                        "the address {} cannot be fetched: {}",
                        url,
                        String::from_utf8_lossy(&out.stderr).trim()
                    ),
                });
            }
        } else {
            // refresh the clone: tags too, so a moved tag is visible
            let fresh = std::process::Command::new("git")
                .args(["-C"])
                .arg(&cache)
                .args(["fetch", "--quiet", "--tags", "--force", "origin"])
                .output();
            let ok = matches!(&fresh, Ok(o) if o.status.success());
            if !ok && version.is_none() {
                // an unpinned dependency has nothing to resolve to offline
                return Err(PackageError::T0520 {
                    what: format!("the address {url} cannot be fetched"),
                });
            }
        }
        if let Some((ma, mi, pa)) = version {
            // the version tag: 1 point 2 point 3 is the tag v1.2.3 or 1.2.3
            let mut checked = false;
            for tag in [format!("v{ma}.{mi}.{pa}"), format!("{ma}.{mi}.{pa}")] {
                let out = std::process::Command::new("git")
                    .args(["-C"])
                    .arg(&cache)
                    .args(["checkout", "--quiet", "--force", &tag])
                    .output();
                match out {
                    Ok(o) if o.status.success() => {
                        checked = true;
                        break;
                    }
                    _ => continue,
                }
            }
            if !checked {
                return Err(PackageError::T0520 {
                    what: format!(
                        "the version {ma} point {mi} point {pa} of {} is not in the repository",
                        dep.name
                    ),
                });
            }
        } else {
            // unpinned: the newest branch head
            let reset = std::process::Command::new("git")
                .args(["-C"])
                .arg(&cache)
                .args(["reset", "--quiet", "--hard", "origin/HEAD"])
                .output();
            match reset {
                Ok(o) if o.status.success() => {}
                _ => {
                    return Err(PackageError::T0520 {
                        what: format!("the address {url} has no branch to use"),
                    });
                }
            }
        }
        // the dependency must be an lykaon package
        if !cache.join("Lykaon.toml").is_file() {
            return Err(PackageError::T0520 {
                what: format!("the fetched {} has no Lykaon.toml", dep.name),
            });
        }
        let checksum = tree_checksum(&cache).map_err(|e| PackageError::T0520 {
            what: format!("the fetched {} cannot be read: {e}", dep.name),
        })?;
        // T0520's second trigger: the checksum differs
        if let Some(lock) = lock {
            if let Some(old) = lock.locked.iter().find(|l| {
                l.name == dep.name
                    && l.version == version.unwrap_or((0, 0, 0))
                    && matches!(&l.source, Source::Git { url: u, .. } if u == url)
            }) {
                if let (Some(old_c), true) = (&old.checksum, version.is_some()) {
                    if old_c != &checksum {
                        return Err(PackageError::T0520 {
                            what: format!(
                                "the checksum of {} differs from the lock (the same version has different content)",
                                dep.name
                            ),
                        });
                    }
                }
            }
        }
        fetched.push((dep.name.clone(), checksum));
    }
    Ok(fetched)
}

/// A deterministic checksum of a fetched package's working tree: SHA-256
/// over every file's relative path and bytes, sorted by path, with the
/// `.git` folder excluded (its index and logs are never package content).
pub fn tree_checksum(root: &Path) -> std::io::Result<String> {
    use sha2::{Digest, Sha256};
    fn walk(base: &Path, dir: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)?
            .filter_map(|e| e.ok().map(|e| e.path()))
            .collect();
        entries.sort();
        for p in entries {
            let name = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
            if name == ".git" {
                continue;
            }
            if p.is_dir() {
                walk(base, &p, files)?;
            } else if p.is_file() {
                files.push(p.strip_prefix(base).unwrap_or(&p).to_path_buf());
            }
        }
        Ok(())
    }
    let mut files = Vec::new();
    walk(root, root, &mut files)?;
    files.sort();
    let mut hasher = Sha256::new();
    for rel in files {
        let mut rel_text = rel.to_string_lossy().replace('\\', "/").into_bytes();
        rel_text.push(0);
        hasher.update(&rel_text);
        let bytes = std::fs::read(root.join(&rel))?;
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

/// Write an lykaon.lock from a Project (used by `lykaon update`). `checksums`
/// holds the (name, checksum) pairs `sync_git_deps` computed.
pub fn write_lockfile(proj: &Project, checksums: &[(String, String)]) -> String {
    let mut out = String::new();
    if let Some(n) = &proj.name {
        out.push_str(&format!("Name is {n}.\n"));
    }
    if let Some((ma, mi, pa)) = proj.version {
        out.push_str(&format!("Version is {ma} point {mi} point {pa}.\n"));
    }
    for dep in &proj.needs {
        match &dep.source {
            Source::Folder(folder) => {
                out.push_str(&format!(
                    "Locked {} from {} at 0 point 0 point 0.\n",
                    dep.name,
                    folder.display()
                ));
            }
            Source::Git { url, version } => {
                let (ma, mi, pa) = version.unwrap_or((0, 0, 0));
                let checksum = checksums
                    .iter()
                    .find(|(n, _)| n == &dep.name)
                    .map(|(_, c)| c.as_str());
                match checksum {
                    Some(c) => out.push_str(&format!(
                        "Locked {} from git {} at {ma} point {mi} point {pa} with checksum {c}.\n",
                        dep.name, url
                    )),
                    None => out.push_str(&format!(
                        "Locked {} from git {} at {ma} point {mi} point {pa}.\n",
                        dep.name, url
                    )),
                }
            }
        }
    }
    out.push_str("Lock allows nothing.\n");
    out
}

/// True when an `lykaon add` argument names a git address (a URL or a
/// scp-like git@ spelling) rather than a local folder.
pub fn looks_like_git_url(arg: &str) -> bool {
    let low = arg.to_ascii_lowercase();
    low.starts_with("https://")
        || low.starts_with("http://")
        || low.starts_with("git://")
        || low.starts_with("ssh://")
        || low.starts_with("git@")
        || (low.starts_with("file://"))
        || low.ends_with(".git")
}

/// The dependency name an `lykaon add <url>` implies: the address's last
/// part without the .git suffix.
pub fn name_from_git_url(url: &str) -> String {
    let stem = url
        .trim_end_matches('/')
        .rsplit('/')
        .next()
        .unwrap_or(url)
        .trim_end_matches(".git");
    stem.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple_project() {
        let text = "Name is myapp.\nVersion is 1 point 2 point 3.\nEntry is main.lykaon.\n";
        let p = parse_project(text).unwrap();
        assert_eq!(p.name, Some("myapp".to_string()));
        assert_eq!(p.version, Some((1, 2, 3)));
        assert_eq!(p.entry, Some("main.lykaon".to_string()));
    }

    #[test]
    fn parse_needs() {
        let text =
            "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds helpers from folder helpers.\n";
        let p = parse_project(text).unwrap();
        assert_eq!(p.needs.len(), 1);
        assert_eq!(p.needs[0].name, "helpers");
        assert_eq!(p.needs[0].source, Source::Folder(PathBuf::from("helpers")));
    }

    #[test]
    fn parse_needs_git() {
        let text = "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds helpers from git https://example.com/helpers.git.\n";
        let p = parse_project(text).unwrap();
        assert_eq!(p.needs.len(), 1);
        assert_eq!(p.needs[0].name, "helpers");
        assert_eq!(
            p.needs[0].source,
            Source::Git {
                url: "https://example.com/helpers.git".to_string(),
                version: None
            }
        );
    }

    #[test]
    fn parse_needs_git_at_version() {
        let text = "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds helpers from git https://example.com/helpers.git at version 1 point 2 point 3.\n";
        let p = parse_project(text).unwrap();
        assert_eq!(
            p.needs[0].source,
            Source::Git {
                url: "https://example.com/helpers.git".to_string(),
                version: Some((1, 2, 3))
            }
        );
    }

    #[test]
    fn parse_needs_git_without_name() {
        // the name defaults to the address's last part
        let text = "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds from git https://example.com/widgettools.git.\n";
        let p = parse_project(text).unwrap();
        assert_eq!(p.needs[0].name, "widgettools");
    }

    #[test]
    fn parse_needs_git_no_address_is_t0520() {
        let text = "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds helpers from git.\n";
        let err = parse_project(text).unwrap_err();
        assert!(matches!(err, PackageError::T0520 { .. }));
    }

    #[test]
    fn missing_name_is_error() {
        let text = "Version is 1 point 0 point 0.\n";
        let err = parse_project(text).unwrap_err();
        assert!(matches!(err, PackageError::T0505 { .. }));
    }

    #[test]
    fn bad_version_is_error() {
        let text = "Name is myapp.\nVersion is one point two.\n";
        let err = parse_project(text).unwrap_err();
        assert!(matches!(err, PackageError::T0514 { .. }));
    }

    #[test]
    fn parse_lockfile_simple() {
        let text = "Name is myapp.\nVersion is 1 point 0 point 0.\nLocked helpers from helpers at 0 point 0 point 0.\nLock allows nothing.\n";
        let l = parse_lockfile(text).unwrap();
        assert_eq!(l.name, Some("myapp".to_string()));
        assert_eq!(l.locked.len(), 1);
        assert_eq!(l.locked[0].name, "helpers");
        assert_eq!(l.locked[0].version, (0, 0, 0));
    }

    #[test]
    fn parse_lockfile_git() {
        let text = "Name is myapp.\nVersion is 1 point 0 point 0.\nLocked helpers from git https://example.com/helpers.git at 1 point 2 point 3.\nLock allows nothing.\n";
        let l = parse_lockfile(text).unwrap();
        assert_eq!(l.locked.len(), 1);
        assert_eq!(l.locked[0].name, "helpers");
        assert_eq!(
            l.locked[0].source,
            Source::Git {
                url: "https://example.com/helpers.git".to_string(),
                version: Some((1, 2, 3))
            }
        );
        assert_eq!(l.locked[0].version, (1, 2, 3));
        assert_eq!(l.locked[0].checksum, None);
    }

    #[test]
    fn parse_lockfile_git_with_checksum() {
        let text = "Name is myapp.\nLocked helpers from git https://example.com/helpers.git at 1 point 2 point 3 with checksum abc123.\nLock allows nothing.\n";
        let l = parse_lockfile(text).unwrap();
        assert_eq!(l.locked[0].version, (1, 2, 3));
        assert_eq!(l.locked[0].checksum, Some("abc123".to_string()));
    }

    #[test]
    fn write_lockfile_roundtrip() {
        let proj = Project {
            name: Some("myapp".to_string()),
            version: Some((1, 2, 3)),
            entry: Some("main.lykaon".to_string()),
            needs: vec![
                Dependency {
                    name: "helpers".to_string(),
                    source: Source::Folder(PathBuf::from("helpers")),
                },
                Dependency {
                    name: "tools".to_string(),
                    source: Source::Git {
                        url: "https://example.com/tools.git".to_string(),
                        version: Some((0, 1, 0)),
                    },
                },
            ],
        };
        let checksums = vec![("tools".to_string(), "deadbeef".to_string())];
        let lock = write_lockfile(&proj, &checksums);
        let relocked = parse_lockfile(&lock).unwrap();
        assert_eq!(relocked.name, proj.name);
        assert_eq!(relocked.version, proj.version);
        assert_eq!(relocked.locked.len(), 2);
        assert_eq!(relocked.locked[1].source, proj.needs[1].source);
        assert_eq!(relocked.locked[1].checksum, Some("deadbeef".to_string()));
    }
}
