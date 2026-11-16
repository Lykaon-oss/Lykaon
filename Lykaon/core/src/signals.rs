//! M4-8 (Appendix K 7.10): the operating system's signals (M4-S79).
//!
//! The runner (the CLI or the built executable's runtime) arms the signals
//! once per process: each signal a program can wait for gets an atomic
//! flag. The interpreter polls the flags at the pause points and runs the
//! registered `When signal ... arrives.` block, or, with none, ends the
//! program after cleaning up with the signal's exit code (interrupt 130,
//! stop 143, hangup 129).
//!
//! Platform honesty (logged): Windows gives the program only the console
//! control signals - Ctrl+C (and Ctrl+Break) arrive as interrupt; stop and
//! hangup exist on Unix only and never fire on Windows. The flag setters
//! come from signal-hook (the one new dependency of M4-8, PART A), which
//! replaces the default disposition, so the arrival is ours to act on.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, OnceLock};

pub struct Flags {
    pub interrupt: Arc<AtomicBool>,
    pub stop: Arc<AtomicBool>,
    pub hangup: Arc<AtomicBool>,
}

static FLAGS: OnceLock<Flags> = OnceLock::new();

/// Arm the signals once per process. The second and later calls do
/// nothing (a process registers each signal once) and still give the
/// flags. Arming requires a signal to have been registered; a second
/// registration of the same signal is refused by the OS layer and is
/// ignored here (the first registration's flag stays in force).
pub fn arm() -> &'static Flags {
    FLAGS.get_or_init(|| {
        let flags = Flags {
            interrupt: Arc::new(AtomicBool::new(false)),
            stop: Arc::new(AtomicBool::new(false)),
            hangup: Arc::new(AtomicBool::new(false)),
        };
        #[cfg(unix)]
        {
            let _ = signal_hook::flag::register(
                signal_hook::consts::signal::SIGINT,
                Arc::clone(&flags.interrupt),
            );
            let _ = signal_hook::flag::register(
                signal_hook::consts::signal::SIGTERM,
                Arc::clone(&flags.stop),
            );
            let _ = signal_hook::flag::register(
                signal_hook::consts::signal::SIGHUP,
                Arc::clone(&flags.hangup),
            );
        }
        #[cfg(windows)]
        {
            // Windows carries the console control signals only: Ctrl+C
            // (SIGINT in the CRT) and Ctrl+Break (SIGBREAK) arrive as
            // interrupt.
            let _ = signal_hook::flag::register(
                signal_hook::consts::signal::SIGINT,
                Arc::clone(&flags.interrupt),
            );
            let _ = signal_hook::flag::register(
                signal_hook::consts::signal::SIGBREAK,
                Arc::clone(&flags.interrupt),
            );
        }
        flags
    })
}

/// Take one arrival of a signal: true when its flag was set (and clears
/// it, so a later arrival is a new arrival). When no runner armed the
/// flags (in-process runs - the test harnesses simulate a person and no
/// signal can arrive), all three read false.
pub fn take_interrupt() -> bool {
    take(&FLAGS.get().map(|f| Arc::clone(&f.interrupt)))
}

pub fn take_stop() -> bool {
    take(&FLAGS.get().map(|f| Arc::clone(&f.stop)))
}

pub fn take_hangup() -> bool {
    take(&FLAGS.get().map(|f| Arc::clone(&f.hangup)))
}

fn take(f: &Option<Arc<AtomicBool>>) -> bool {
    match f {
        Some(flag) => flag.swap(false, Ordering::Relaxed),
        None => false,
    }
}

/// A test hook: set a signal's flag directly, so an in-process run can
/// exercise the poll-and-run path (no signal can be sent to the test
/// process from a test).
#[doc(hidden)]
pub fn test_fire(signal: crate::sem::SignalName) {
    let flags = arm();
    let f = match signal {
        crate::sem::SignalName::Interrupt => &flags.interrupt,
        crate::sem::SignalName::Stop => &flags.stop,
        crate::sem::SignalName::Hangup => &flags.hangup,
    };
    f.store(true, Ordering::Relaxed);
}
