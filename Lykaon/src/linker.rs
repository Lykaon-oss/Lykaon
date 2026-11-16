//! Locate the Microsoft x64 toolchain (link.exe and the CRT/SDK libraries)
//! and link an lykaon object against liblykaon_rt (M3 backend, section 9:
//! Microsoft x64 first). The detection order is explicit overrides, then
//! vswhere, then a version-ordered scan of the Visual Studio and Windows SDK
//! install roots — the same paths the environment probe verified.

use std::path::{Path, PathBuf};

/// Where to run link.exe from, and which directories to search for the CRT
/// and SDK import libraries (/LIBPATH list).
pub struct Toolchain {
    pub link: PathBuf,
    pub lib_dirs: Vec<PathBuf>,
}

impl Toolchain {
    pub fn describe(&self) -> String {
        let mut s = self.link.display().to_string();
        for d in &self.lib_dirs {
            s.push_str(&format!("  /LIBPATH:{}", d.display()));
        }
        s
    }
}

fn program_files_x86() -> String {
    std::env::var("ProgramFiles(x86)").unwrap_or_else(|_| "C:\\Program Files (x86)".to_string())
}

fn program_files() -> String {
    std::env::var("ProgramFiles").unwrap_or_else(|_| "C:\\Program Files".to_string())
}

/// The newest child directory whose name starts with a digit (14.51.36231,
/// 10.0.26100.0, ...), compared numerically component by component.
fn newest_dir(root: &Path) -> Option<PathBuf> {
    let mut best: Option<(Vec<u32>, PathBuf)> = None;
    for e in std::fs::read_dir(root).ok()?.flatten() {
        let p = e.path();
        if !p.is_dir() {
            continue;
        }
        let name = e.file_name().to_string_lossy().to_string();
        if !name.chars().next().is_some_and(|c| c.is_ascii_digit()) {
            continue;
        }
        let key: Vec<u32> = name
            .split(['.', '-'])
            .filter_map(|x| x.parse::<u32>().ok())
            .collect();
        if key.is_empty() {
            continue;
        }
        if best.as_ref().is_none_or(|(b, _)| key > *b) {
            best = Some((key, p));
        }
    }
    best.map(|(_, p)| p)
}

/// Visual Studio install roots to scan for VC\\Tools\\MSVC.
fn vs_roots() -> Vec<PathBuf> {
    vec![
        PathBuf::from(format!("{}\\Microsoft Visual Studio", program_files_x86())),
        PathBuf::from(format!("{}\\Microsoft Visual Studio", program_files())),
    ]
}

fn vswhere_install() -> Option<PathBuf> {
    let vswhere = PathBuf::from(program_files_x86())
        .join("Microsoft Visual Studio")
        .join("Installer")
        .join("vswhere.exe");
    if !vswhere.exists() {
        return None;
    }
    let out = std::process::Command::new(&vswhere)
        .args([
            "-latest",
            "-products",
            "*",
            "-requires",
            "Microsoft.VisualStudio.Component.VC.Tools.x86.x64",
            "-property",
            "installationPath",
        ])
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .map(PathBuf::from)
}

/// Windows SDK library directories that hold um/ (kernel32.lib) and ucrt/.
fn sdk_dirs() -> Vec<PathBuf> {
    let root = PathBuf::from(program_files_x86())
        .join("Windows Kits")
        .join("10")
        .join("Lib");
    match newest_dir(&root) {
        Some(v) => vec![v.join("um").join("x64"), v.join("ucrt").join("x64")],
        None => Vec::new(),
    }
}

/// Detect the toolchain: Lykaon_LINK / Lykaon_LIBS overrides, then vswhere, then
/// the plain version scan, then lld-link from the Rust toolchain as a last
/// resort (same link-line arguments; the CRT/SDK libs are looked up in the
/// same place).
pub fn detect() -> Result<Toolchain, String> {
    // 1. explicit overrides
    if let Ok(link) = std::env::var("Lykaon_LINK") {
        let p = PathBuf::from(&link);
        if !p.exists() {
            return Err(format!("Lykaon_LINK points at nothing: {link}"));
        }
        let mut lib_dirs = Vec::new();
        if let Ok(libs) = std::env::var("Lykaon_LIBS") {
            for d in libs.split(';') {
                if !d.is_empty() {
                    lib_dirs.push(PathBuf::from(d));
                }
            }
        }
        return Ok(Toolchain { link: p, lib_dirs });
    }

    // 2. vswhere, then a scan of the usual install roots
    let mut installs: Vec<PathBuf> = Vec::new();
    if let Some(i) = vswhere_install() {
        installs.push(i);
    }
    for root in vs_roots() {
        if let Ok(rd) = std::fs::read_dir(&root) {
            for e in rd.flatten() {
                if e.path().is_dir() {
                    installs.push(e.path());
                }
            }
        }
    }
    for ins in &installs {
        let tools = ins.join("VC").join("Tools").join("MSVC");
        let Some(msvc) = newest_dir(&tools) else {
            continue;
        };
        let link = msvc
            .join("bin")
            .join("Hostx64")
            .join("x64")
            .join("link.exe");
        if link.exists() {
            let mut lib_dirs = vec![msvc.join("lib").join("x64")];
            lib_dirs.extend(sdk_dirs());
            return Ok(Toolchain { link, lib_dirs });
        }
    }

    // 3. rust-lld ships with the toolchain and speaks lld-link's dialect
    if let Ok(home) = std::env::var("RUSTUP_HOME") {
        for tc in [
            "stable-x86_64-pc-windows-msvc",
            "nightly-x86_64-pc-windows-msvc",
        ] {
            let lld = PathBuf::from(&home)
                .join("toolchains")
                .join(tc)
                .join("lib")
                .join("rustlib")
                .join("x86_64-pc-windows-msvc")
                .join("bin")
                .join("lld-link.exe");
            if lld.exists() {
                let mut lib_dirs = Vec::new();
                for root in vs_roots() {
                    if let Ok(rd) = std::fs::read_dir(&root) {
                        for e in rd.flatten() {
                            let tools = e.path().join("VC").join("Tools").join("MSVC");
                            if let Some(msvc) = newest_dir(&tools) {
                                lib_dirs.push(msvc.join("lib").join("x64"));
                            }
                        }
                    }
                }
                lib_dirs.extend(sdk_dirs());
                return Ok(Toolchain {
                    link: lld,
                    lib_dirs,
                });
            }
        }
    }

    Err(
        "no Microsoft x64 linker found. Install VS Build Tools (Desktop development with \
         C++), or set Lykaon_LINK to link.exe and Lykaon_LIBS to the /LIBPATH libraries \
         (a ';' list)."
            .to_string(),
    )
}

/// Link one object plus liblykaon_rt into a console executable. The runtime
/// library provides `main`; the object provides `lykaon_main` (and the data
/// symbols it references).
pub fn link(obj: &Path, rt_lib: &Path, out: &Path) -> Result<(), String> {
    let tc = detect()?;
    let mut cmd = std::process::Command::new(&tc.link);
    cmd.arg("/NOLOGO")
        .arg("/MACHINE:X64")
        .arg("/SUBSYSTEM:CONSOLE")
        .arg("/INCREMENTAL:NO")
        .arg(format!("/OUT:{}", out.display()))
        .arg(obj)
        .arg(rt_lib);
    for d in &tc.lib_dirs {
        cmd.arg(format!("/LIBPATH:{}", d.display()));
    }
    cmd.args([
        "libcmt.lib",
        "libvcruntime.lib",
        "libucrt.lib",
        "kernel32.lib",
        "user32.lib",
        "ws2_32.lib",
        "advapi32.lib",
        "userenv.lib",
        "ntdll.lib",
    ]);
    let r = cmd
        .output()
        .map_err(|e| format!("cannot run {}: {e}", tc.link.display()))?;
    if !r.status.success() {
        return Err(format!(
            "linking failed:\n{}\n{}",
            String::from_utf8_lossy(&r.stdout),
            String::from_utf8_lossy(&r.stderr)
        ));
    }
    Ok(())
}

/// Where liblykaon_rt lives: built from this workspace (`cargo build` builds
/// it, it is a workspace member), possibly in the rt/ subdirectory's own
/// target when someone built it alone. The search also starts from the
/// running exe's folder and its parent, so a front copied into `dist/` still
/// finds `<repo>/Lykaon/target/<profile>/lykaon_rt.lib`.
pub fn find_rt_lib() -> Result<PathBuf, String> {
    if let Ok(p) = std::env::var("Lykaon_RT_LIB") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Ok(p);
        }
        return Err(format!("Lykaon_RT_LIB points at nothing: {p:?}"));
    }
    // The static library's name differs by host: MSVC names it
    // lykaon_rt.lib, a Unix toolchain names it liblykaon_rt.a.
    let names: &[&str] = if cfg!(windows) {
        &["lykaon_rt.lib"]
    } else {
        &["liblykaon_rt.a"]
    };
    // Search roots, nearest first: every ancestor of the working folder and
    // of the running exe (up to four levels each). Each root is then probed at
    // `target/`, `Lykaon/target/` (a front run from the repository root or
    // dist/) and `rt/target/` (the rt package built on its own). Ancestors are
    // what make a build launched from a scratch folder find the workspace,
    // and what let the exe under `Lykaon/target/debug` reach
    // `Lykaon/target/debug/lykaon_rt.lib` without a working-directory hint.
    let mut roots: Vec<PathBuf> = Vec::new();
    let mut push_ancestors = |start: Option<&Path>| {
        let mut cur = start.map(Path::to_path_buf);
        for _ in 0..5 {
            let Some(d) = cur else { break };
            if !roots.contains(&d) {
                roots.push(d.clone());
            }
            cur = d.parent().map(Path::to_path_buf);
        }
    };
    push_ancestors(std::env::current_dir().ok().as_deref());
    push_ancestors(
        std::env::current_exe()
            .ok()
            .and_then(|e| e.parent().map(Path::to_path_buf))
            .as_deref(),
    );
    let mut cands: Vec<PathBuf> = Vec::new();
    for profile in ["debug", "release"] {
        for name in names {
            for root in &roots {
                cands.push(root.join("target").join(profile).join(name));
                cands.push(root.join("Lykaon").join("target").join(profile).join(name));
                cands.push(root.join("rt").join("target").join(profile).join(name));
            }
        }
    }
    for c in &cands {
        if c.exists() {
            return Ok(c.clone());
        }
    }
    Err("liblykaon_rt was not built yet: run cargo build in the lykaon workspace (it builds rt as a member), or set Lykaon_RT_LIB.".to_string())
}

/// The default suffix for an executable on this host: `.exe` on Windows,
/// nothing on Unix.
pub fn exe_suffix() -> &'static str {
    if cfg!(windows) { ".exe" } else { "" }
}

/// Link an object into a runnable program on whichever host the compiler is
/// running on. Windows uses the MSVC link line above; Unix hands the object
/// and the static runtime archive to the C driver (`cc`), which supplies the
/// system startup files and libc.
pub fn link_exe(obj: &Path, rt_lib: &Path, out: &Path) -> Result<(), String> {
    if cfg!(windows) {
        link(obj, rt_lib, out)
    } else {
        link_unix(obj, rt_lib, out)
    }
}

/// Link on a Unix host: `cc -o out obj liblykaon_rt.a -lpthread -ldl -lm`.
/// `Lykaon_LINK` overrides the driver, matching the Windows override.
fn link_unix(obj: &Path, rt_lib: &Path, out: &Path) -> Result<(), String> {
    let cc = std::env::var("Lykaon_LINK").unwrap_or_else(|_| "cc".to_string());
    let mut cmd = std::process::Command::new(&cc);
    cmd.arg("-o").arg(out).arg(obj).arg(rt_lib);
    cmd.args(["-lpthread", "-ldl", "-lm"]);
    let r = cmd.output().map_err(|e| format!("cannot run {cc}: {e}"))?;
    if !r.status.success() {
        return Err(format!(
            "linking failed:\n{}\n{}",
            String::from_utf8_lossy(&r.stdout),
            String::from_utf8_lossy(&r.stderr)
        ));
    }
    Ok(())
}
