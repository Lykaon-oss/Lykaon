//! Lexer: turn text into tokens as in Reference 1 (p.313).
//! Tokenizes a single code line (not raw text).

use crate::diagnostics::Diagnostic;

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    Word { text: String, lower: String },
    Whole { value: i64 },
    Decimal { value: f64 },
    Negative { value: i64 }, // "minus N"
    YesNo { value: bool },
    Missing,
    Nothing,
    Period,
    Eof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WordClass {
    Hard,        // fixed meaning, never part of a name
    Soft,        // library word, may be a name
    Declaration, // To / A / An / Constant / Changeable at start of sentence
    Action,      // starts a sentence (Say, Ask, Set, ...)
    Article,     // the / a / an
    Pronoun,     // it / its / them
    Ordinary,    // regular word
}

/// Words with one fixed meaning in every sentence (Appendix A, p.196-198).
pub fn hard_words() -> &'static [&'static str] {
    &[
        "say",
        "ask",
        "if",
        "otherwise",
        "repeat",
        "for",
        "each",
        "in",
        "stop",
        "skip",
        "to",
        "give",
        "lend",
        "copy",
        "share",
        "set",
        "put",
        "add",
        "remove",
        "try",
        "fail",
        "pass",
        "look",
        "at",
        "when",
        "use",
        "close",
        "start",
        "wait",
        "send",
        "receive",
        "do",
        "be",
        "careful",
        "together",
        "test",
        "check",
        "constant",
        "changeable",
        "note",
        "about",
        "example",
        "tagged",
        "requires",
        "ensures",
        "always",
        "is",
        "are",
        "not",
        "and",
        "or",
        "plus",
        "minus",
        "times",
        "divided",
        "by",
        "between",
        "more",
        "less",
        "least",
        "most",
        "than",
        "with",
        "from",
        "of",
        "under",
        "as",
        "it",
        "its",
        "them",
        "that",
        "literally",
        "lines",
        "without",
        "newline",
        "fallback",
        "yes",
        "no",
        "missing",
        "there",
        "maybe",
        "nothing",
        "can",
        "must",
        "has",
        "anything",
        "forever",
        "while",
    ]
}

/// Declaration words at the start of a sentence.
fn is_declaration(word: &str) -> bool {
    matches!(word, "to" | "a" | "an" | "constant" | "changeable")
}

/// Action words that start a sentence.
fn is_action(word: &str) -> bool {
    matches!(
        word,
        "say"
            | "ask"
            | "set"
            | "stop"
            | "skip"
            | "repeat"
            | "for"
            | "if"
            | "otherwise"
            | "note"
            | "about"
            | "changeable"
            | "constant"
    )
}

/// Words that read as articles (Ch.3). They are ordinary words the parser
/// recognizes by position, so they are not in `hard_words`; the UI's
/// highlighter still colours them.
pub fn article_words() -> &'static [&'static str] {
    &["the", "a", "an"]
}

fn is_article(word: &str) -> bool {
    article_words().contains(&word)
}

fn is_pronoun(word: &str) -> bool {
    matches!(word, "it" | "its" | "them")
}

fn classify(lower: &str) -> WordClass {
    if hard_words().contains(&lower) {
        if is_declaration(lower) {
            return WordClass::Declaration;
        }
        if is_action(lower) {
            return WordClass::Action;
        }
        if is_article(lower) {
            return WordClass::Article;
        }
        if is_pronoun(lower) {
            return WordClass::Pronoun;
        }
        return WordClass::Hard;
    }
    WordClass::Soft
}

pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    /// Tokenize the whole line. Returns (tokens, lex_error_diagnostic).
    pub fn tokenize(mut self) -> (Vec<Token>, Option<Diagnostic>) {
        let mut tokens = Vec::new();
        let mut err = None;
        while self.pos < self.input.len() {
            self.skip_spaces();
            if self.pos >= self.input.len() {
                break;
            }
            let ch = self.input[self.pos..].chars().next().unwrap();
            if ch.is_ascii_digit() {
                match self.read_number() {
                    Ok(tok) => {
                        // T0011: a name begins with a digit (`2nd place`)
                        let next = self.input.as_bytes().get(self.pos).copied();
                        if next.map_or(false, |n| n.is_ascii_alphabetic()) {
                            err = Some(Diagnostic::error(
                                "T0011",
                                "Name starts with a digit.".to_string(),
                                "".to_string(),
                                0,
                                self.input.to_string(),
                                self.pos,
                                self.pos + 1,
                                "A name begins with a digit.".to_string(),
                                "Begin the name with a letter.".to_string(),
                            ));
                            break;
                        }
                        tokens.push(tok)
                    }
                    Err(e) => {
                        err = Some(e);
                        break;
                    }
                }
            } else if ch.is_ascii_alphabetic() || ch.is_alphabetic() {
                tokens.push(self.read_word());
            } else if ch == '"' {
                // T0008: Lykaon has no quoted text
                err = Some(Diagnostic::error(
                    "T0008",
                    "Quote in code.".to_string(),
                    "".to_string(),
                    0,
                    self.input.to_string(),
                    self.pos,
                    self.pos + 1,
                    "A quote mark is used in code. Lykaon has no quoted text.".to_string(),
                    "Write the word without quotes.".to_string(),
                ));
                break;
            } else if ch == ',' {
                // T0009: items join with the word and
                err = Some(Diagnostic::error(
                    "T0009",
                    "Comma in code.".to_string(),
                    "".to_string(),
                    0,
                    self.input.to_string(),
                    self.pos,
                    self.pos + 1,
                    "A comma is used to join items.".to_string(),
                    "Join items with the word and.".to_string(),
                ));
                break;
            } else if ch == '.' {
                // Period: end of sentence or decimal point.
                // Decimal point only between two digits.
                let next = self.input.as_bytes().get(self.pos + 1);
                if next.map_or(false, |n| n.is_ascii_digit()) {
                    // handled as part of number only if digit before; here a lone '.'
                    // between digits is consumed by read_number when a digit precedes.
                    // A stray '.' is an error (T0005) reported by splitter/parser.
                    tokens.push(Token::Period);
                    self.pos += 1;
                } else {
                    tokens.push(Token::Period);
                    self.pos += 1;
                }
            } else if ch.is_ascii_punctuation() {
                // T0007: an operator or bracket in code (the book's
                // `Total is 2 + 3.`); the other ASCII punctuation that is
                // not a quote, comma or period is a symbol too.
                err = Some(Diagnostic::error(
                    "T0007",
                    "Symbol in code.".to_string(),
                    "".to_string(),
                    0,
                    self.input.to_string(),
                    self.pos,
                    self.pos + 1,
                    "A symbol such as a bracket or an operator appears in code.".to_string(),
                    "Use words, such as 2 plus 3.".to_string(),
                ));
                break;
            } else {
                // T0010: a character that cannot be part of a word (a
                // non-ASCII symbol); T0007 owns the code symbols above.
                err = Some(Diagnostic::error(
                    "T0010",
                    "Invalid character.".to_string(),
                    "".to_string(),
                    0,
                    self.input.to_string(),
                    self.pos,
                    self.pos + 1,
                    "A character cannot be part of a word.".to_string(),
                    "Use letters and digits.".to_string(),
                ));
                break;
            }
        }
        tokens.push(Token::Eof);
        (tokens, err)
    }

    fn skip_spaces(&mut self) {
        while self.pos < self.input.len() && self.input.as_bytes()[self.pos] == b' ' {
            self.pos += 1;
        }
    }

    fn read_word(&mut self) -> Token {
        let start = self.pos;
        while self.pos < self.input.len() {
            // Iterate by chars: a byte cast to char would walk into the
            // middle of multi-byte UTF-8 letters (e.g. an em dash).
            let ch = self.input[self.pos..].chars().next().unwrap();
            if ch.is_ascii_alphanumeric() || ch.is_alphabetic() {
                self.pos += ch.len_utf8();
            } else {
                break;
            }
        }
        let text = self.input[start..self.pos].to_string();
        let lower = text.to_ascii_lowercase();
        match lower.as_str() {
            "yes" => Token::YesNo { value: true },
            "no" => Token::YesNo { value: false },
            "missing" => Token::Missing,
            "nothing" => Token::Nothing,
            _ => Token::Word { text, lower },
        }
    }

    fn read_number(&mut self) -> Result<Token, Diagnostic> {
        let start = self.pos;
        while self.pos < self.input.len() && self.input.as_bytes()[self.pos].is_ascii_digit() {
            self.pos += 1;
        }
        let digits = &self.input[start..self.pos];
        // decimal point?
        if self.pos < self.input.len() && self.input.as_bytes()[self.pos] == b'.' {
            let after = self.pos + 1;
            if after < self.input.len() && self.input.as_bytes()[after].is_ascii_digit() {
                self.pos = after;
                while self.pos < self.input.len()
                    && self.input.as_bytes()[self.pos].is_ascii_digit()
                {
                    self.pos += 1;
                }
                let value: f64 = self.input[start..self.pos].parse().unwrap();
                return Ok(Token::Decimal { value });
            }
        }
        let value: i64 = match digits.parse() {
            Ok(v) => v,
            Err(_) => {
                return Err(Diagnostic::error(
                    "T0134",
                    "Number too large.".to_string(),
                    "".to_string(),
                    0,
                    digits.to_string(),
                    0,
                    digits.len(),
                    "A whole number is larger than 64 bits.".to_string(),
                    "Write it as big number.".to_string(),
                ));
            }
        };
        Ok(Token::Whole { value })
    }
}

pub fn classify_word(lower: &str) -> WordClass {
    classify(lower)
}
