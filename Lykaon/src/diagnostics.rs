//! M1a diagnostics. Cause/Fix wording comes only from Reference 2 (book p.315+).
//! The What line states the name with the words of your program.

use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: &'static str,
    pub what: String,
    pub file: String,
    pub line: usize,
    pub sentence: String,
    pub mark_lo: usize, // byte index into sentence (start of marked region)
    pub mark_hi: usize, // byte index into sentence (end of marked region)
    pub why: String,
    pub fix: String,
}

impl Diagnostic {
    pub fn error(
        code: &'static str,
        what: String,
        file: String,
        line: usize,
        sentence: String,
        mark_lo: usize,
        mark_hi: usize,
        why: String,
        fix: String,
    ) -> Self {
        Self {
            severity: Severity::Error,
            code,
            what,
            file,
            line,
            sentence,
            mark_lo,
            mark_hi,
            why,
            fix,
        }
    }

    pub fn warning(
        code: &'static str,
        what: String,
        file: String,
        line: usize,
        sentence: String,
        mark_lo: usize,
        mark_hi: usize,
        why: String,
        fix: String,
    ) -> Self {
        Self {
            severity: Severity::Warning,
            code,
            what,
            file,
            line,
            sentence,
            mark_lo,
            mark_hi,
            why,
            fix,
        }
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = if self.severity == Severity::Error {
            "Error"
        } else {
            "Warning"
        };
        writeln!(f, "{}: {} ({})", kind, self.what, self.code)?;
        let where_prefix = format!("Where: {}, line {}: ", self.file, self.line);
        writeln!(f, "{}{}", where_prefix, self.sentence)?;
        let width = (self.mark_hi.saturating_sub(self.mark_lo)).max(1);
        let mark = " ".repeat(where_prefix.len() + self.mark_lo) + &"^".repeat(width);
        writeln!(f, "{}", mark)?;
        writeln!(f, "Why: {}", self.why)?;
        writeln!(f, "Fix: {}", self.fix)
    }
}
