//! Formatter: print the canonical layout of any source file.
//! One sentence per line, 4 spaces per indent level, LF endings, no BOM,
//! no trailing spaces, at most one blank line in a row.

use crate::splitter::{Sentence, split_source};

pub fn format(source: &str) -> String {
    let bytes = source.as_bytes();
    let start = if bytes.len() >= 3 && bytes[0] == 0xEF && bytes[1] == 0xBB && bytes[2] == 0xBF {
        3
    } else {
        0
    };
    let text = &source[start..];
    let normalized = text.replace("\r\n", "\n").replace('\r', "\n");

    let split = split_source(&normalized, "<source>");
    let (all, roots) = match split {
        Ok(s) => (s.all, s.roots),
        Err(_) => (Vec::new(), Vec::new()),
    };

    let mut out = String::new();
    emit_block(&all, &roots, 0, &mut out);
    // ensure exactly one trailing newline
    if !out.is_empty() && !out.ends_with('\n') {
        out.push('\n');
    }
    out
}

fn emit_block(all: &[Sentence], indices: &[usize], level: usize, out: &mut String) {
    let indent = " ".repeat(level * 4);
    for (_pos, &idx) in indices.iter().enumerate() {
        let s = &all[idx];
        let mut line = s.text.clone();
        if !line.ends_with('.') {
            line.push('.');
        }
        out.push_str(&indent);
        out.push_str(&line);
        out.push('\n');
        if !s.children.is_empty() {
            emit_block(all, &s.children, level + 1, out);
        }
    }
}
