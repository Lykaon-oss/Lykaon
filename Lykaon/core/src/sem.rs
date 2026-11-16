//! The typed tree and value model (Ch.67): the shared data types of the
//! compiler (semantic layer), the interpreter and the native runtime.
//! The types live in lykaon-core so that liblykaon_rt (the runtime library
//! linked into built programs) holds the very same value model as the
//! interpreter that defines what every program means.
// ---------------------------------------------------------------- kinds

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    Whole,
    Decimal,
    Text,
    Boolean,
    Big,
    Letter,                                   // a single Unicode letter (Ch.14)
    List(Box<Kind>),                          // list of T
    Pair(Box<Kind>, Box<Kind>),               // pair of A and B
    Array(Box<Kind>),                         // array of N T
    Map(Box<Kind>, Box<Kind>),                // map of K to V
    Set(Box<Kind>),                           // set of T
    Queue(Box<Kind>),                         // queue of T
    Maybe(Box<Kind>),                         // maybe T
    Record(String, Vec<(String, Kind)>), // A person has name as K and ... (the type name first)
    Limited(Vec<String>), // anything that can VERB and VERB (M3): a limit, checked per use
    Enum(Vec<(String, Vec<(String, Kind)>)>), // A name is V1 or V2 with parts
    Share,                // a counted handle (ch.28, M2-S3)
    WeakShare,            // a non-owning link (ch.28, M2-S44)
    /// M4 (Appendix K): channel of T (M4-G7).
    Channel(Box<Kind>),
    /// M4 (Appendix K): guarded V (M4-G8); the inner kind is the guarded
    /// value's kind.
    Guarded(Box<Kind>),
    /// M4 (Appendix K): atomic number (M4-G9).
    Atomic,
    /// M4 (Appendix K): counter (M4-G10).
    Counter,
    /// M4 (Appendix K): connection (M4-S73): one live WebSocket
    /// connection. A copy kind that is storable in lists, maps and sets,
    /// prints as the word connection, and is useless for arithmetic.
    Connection,
    /// M4-7 (Appendix K S50): a calendar day in the proleptic Gregorian
    /// calendar.
    Date,
    /// M4-7 (Appendix K S51): an instant with a time zone.
    Moment,
    /// M4-7 (Appendix K S52): a signed length with nanosecond precision.
    /// Months and years are not units in M4.
    Duration,
    /// M4-7 (Appendix K S56): a secret of the inner kind (text in this
    /// cut). It prints as hidden, is never logged, cannot be compared,
    /// cannot be converted, and is zeroed when dropped.
    Secret(Box<Kind>),
    Missing,
    Unknown,
}

// ---------------------------------------------------------------- values

/// A part of a text pattern (ch.14, M2-G31).
#[derive(Clone, Debug)]
pub enum Pat {
    Word(String),         // a plain word matches itself
    Digits,               // digits
    Letters,              // letters
    Spaces,               // spaces
    Anything,             // anything
    OneOrMore(Box<Pat>),  // one or more X
    Optional(Box<Pat>),   // optional X
    StartsWith(Box<Pat>), // starts with X
    EndsWith(Box<Pat>),   // ends with X
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Whole(i64),
    Dec(f64),
    Text(String),
    Boolean(bool),
    Missing,
    Big(Vec<u32>),
    List(Vec<Value>),
    Pair(Box<Value>, Box<Value>),
    Map(Vec<(Value, Value)>),             // insertion-ordered map
    Set(Vec<Value>),                      // set of values
    Queue(Vec<Value>),                    // ring buffer queue
    Array(Vec<Option<Value>>),            // fixed-size array; None = not yet set (T0615)
    Record(String, Vec<(String, Value)>), // a value of record type + the type name (ch.20, M3)
    /// A function value: a plain function (no captures) or a closure.
    /// Captures are (name, value) pairs taken from the frame where the
    /// local `To` was written (M3-D2).
    Closure {
        func: String,
        captures: Vec<(String, Value)>,
    },
    /// A dynamic-dispatch value (`as any speaker`, ch.23): a pair of the
    /// value and the kind it carries; the table pointer is the impl lookup
    /// by the type name (M3-S18).
    Dyn {
        type_name: String,
        value: Box<Value>,
    },
    /// A lazy sequence from a generator call (ch.25, M3-S31). Items are
    /// pulled one at a time.
    Generator(GeneratorHandle),
    FunctionRef(String), // a function name used where a function is expected (M3-S21)
    Enum {
        variant: String,
        parts: Vec<Value>,
    },
    Maybe(Option<Box<Value>>),
    Share(Box<Value>),     // a counted handle (ch.28)
    WeakShare(Box<Value>), // a non-owning link (ch.28)
    /// M4 (Appendix K, S11..S15): a channel of T. Both ends (sender and
    /// receiver) live in the one value; copies share the ONE state through
    /// the Rc, so every name holding the channel sees the same queue.
    Channel(std::rc::Rc<std::cell::RefCell<ChannelState>>),
    /// M4-S16: a guarded value. Each sentence that reads or sets it takes
    /// the lock; in the eager first cut the single worker makes the lock
    /// unobservable (deviation logged), so this is a plain cell.
    Guarded(Box<Value>),
    /// M4-S19: an atomic number. It starts at 0 and changes only with
    /// Add ... atomically. The value read out of it is the plain number.
    Atomic(i64),
    /// M4-S20: a counter, an atomic whole number that starts at 0. It
    /// changes with Add; Say prints its value.
    Counter(i64),
    /// M4-7 (Appendix K S50): a date, (year, month 1..12, day 1..31) in
    /// the proleptic Gregorian calendar. Validated at construction
    /// (impossible date is T0620).
    Date(i64, i64, i64),
    /// M4-7 (Appendix K S51): a moment, an instant with a time zone. The
    /// instant is nanoseconds since the Unix epoch (i128); the zone holds
    /// the IANA name the value was given in (printing uses the zone's
    /// offset AT this instant).
    Moment {
        nanos: i128,
        zone: String,
    },
    /// M4-7 (Appendix K S52): a duration, signed nanoseconds.
    Duration(i128),
    /// M4-7 (Appendix K S56): a secret of the inner kind (text in this
    /// cut). It prints as hidden, is never logged, cannot be compared,
    /// cannot be converted, and is zeroed when dropped (the zeroing
    /// lives in SecretInner's Drop, since a Drop on Value itself would
    /// forbid moving fields out of the other variants).
    Secret(Box<SecretInner>),
    /// M4 (Appendix K, S73): one live connection. The id is the
    /// server-side handle; the socket itself lives in the server's
    /// connection table. Copies share nothing (the id is the value).
    Conn(u64),
}

/// M4-7 (S56): the contents of a secret (text in this cut). It is
/// zeroed byte by byte when dropped.
#[derive(Clone, Debug, PartialEq)]
pub struct SecretInner(pub Value);

impl Drop for SecretInner {
    fn drop(&mut self) {
        if let Value::Text(t) = &mut self.0 {
            for b in unsafe { t.as_bytes_mut() } {
                *b = 0;
            }
        }
    }
}

/// M4 (Appendix K, S11..S15): the shared state of one channel.
#[derive(Debug)]
pub struct ChannelState {
    /// Items waiting to be received, oldest first.
    pub queue: Vec<Value>,
    /// M4-S11: holds at most 64 items unless holding N was written.
    pub cap: usize,
    /// The declared element kind (channel of T), for Send checks.
    pub item: Option<Kind>,
    /// M4-S14: a channel closes when every sender is dropped. The eager
    /// first cut does not track sender drops yet (deviation logged); this
    /// flag is the hook the worker-pool increment will drive.
    pub closed: bool,
}

/// Channels compare by what they still hold (the queue) and their closed
/// state; capacity and declared kind are construction details. Rc and
/// RefCell pass through to this impl, so Value's derived PartialEq works.
impl PartialEq for ChannelState {
    fn eq(&self, other: &Self) -> bool {
        self.closed == other.closed
            && self.queue.len() == other.queue.len()
            && self
                .queue
                .iter()
                .zip(other.queue.iter())
                .all(|(a, b)| a == b)
    }
}

/// A generator handle (ch.25): the generator runs only as far as items are
/// asked for (M3-S31). Each pull suspends the body at its next Hand back
/// (the block graph plus the frozen frame in `resume`) and resumes there for
/// the next item; when the body ends, `finished` holds. Built-in lazy kinds
/// (first N fibonacci / primes, M3-D12) do not go through this handle.
/// Clone shares the underlying sequence, so a copied generator continues
/// where the original left off.
/// The suspended position of a generator body between pulls (ch.25): where
/// the program counter stopped (the block graph of the body, built once),
/// the loop-counter values of that graph, and the frozen frame (locals,
/// scopes, pronouns). Shared through the handle, so a copied generator
/// continues where the original left off.
#[derive(Clone, Debug, Default)]
pub struct GenState {
    /// The body has run far enough to be resumable (or is finished).
    pub started: bool,
    /// A pull is executing this handle's body right now (re-entrant pulls
    /// take the collect-all path instead of suspending).
    pub pull_active: bool,
    /// Program counter into `handle.mir`: (block, next step index).
    pub block: usize,
    pub step: usize,
    /// (current, limit) per block-graph counter id.
    pub gcounters: Vec<(i64, i64)>,
    /// Counters already bounds-initialised by their ForInit step.
    pub bounds_set: Vec<bool>,
    /// The frozen frame, or None before the first pull.
    pub frame_state: Option<GenFrame>,
}

/// The parts of an interpreter frame a suspended generator needs (a plain
/// data mirror the handle can own; interp.rs converts both ways).
#[derive(Clone, Debug, Default)]
pub struct GenFrame {
    /// Per scope: bindings in insertion order, and the order itself.
    pub scopes: Vec<(Vec<(String, Value)>, Vec<String>)>,
    /// Loop counters of delegated statements.
    pub counters: Vec<(i64, i64)>,
    pub last_result: Option<Value>,
    pub last_shown: String,
    pub where_item: Option<Value>,
}

#[derive(Debug)]
pub struct GeneratorHandle {
    pub func: String,               // the generator function's name
    pub args: Vec<(String, Value)>, // call inputs
    /// Every item handed back so far, in order.
    pub cache: std::sync::Arc<std::sync::Mutex<Vec<Value>>>,
    /// The body ended and will hand back no more.
    pub finished: std::sync::Arc<std::sync::atomic::AtomicBool>,
    /// The body's block graph, built once at creation (ch.25 suspension).
    pub mir: std::sync::Arc<crate::mir::ProgramMir>,
    /// Where the body starts in that graph.
    pub entry: usize,
    /// Captured names and their values, frozen where the generator was
    /// created (M3-D2 snapshot rule; inputs excluded).
    pub caps: Vec<(String, Value)>,
    /// The suspension state shared by all clones of the handle.
    pub resume: std::sync::Arc<std::sync::Mutex<GenState>>,
}

impl GeneratorHandle {
    pub fn new(
        func: String,
        args: Vec<(String, Value)>,
        cache: std::sync::Arc<std::sync::Mutex<Vec<Value>>>,
        finished: std::sync::Arc<std::sync::atomic::AtomicBool>,
        mir: std::sync::Arc<crate::mir::ProgramMir>,
        entry: usize,
        caps: Vec<(String, Value)>,
    ) -> Self {
        GeneratorHandle {
            func,
            args,
            cache,
            finished,
            mir,
            entry,
            caps,
            resume: std::sync::Arc::new(std::sync::Mutex::new(GenState::default())),
        }
    }
}

impl Clone for GeneratorHandle {
    fn clone(&self) -> Self {
        GeneratorHandle {
            func: self.func.clone(),
            args: self.args.clone(),
            cache: self.cache.clone(),
            finished: self.finished.clone(),
            mir: self.mir.clone(),
            entry: self.entry,
            caps: self.caps.clone(),
            resume: self.resume.clone(),
        }
    }
}

impl PartialEq for GeneratorHandle {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

/// Can the generator body suspend at every Hand back? (ch.25, M3-D12)
/// Hand back must stay in positions the block graph flattens: the body list
/// itself, or the bodies of If / Repeat / for-range loops. A Hand back hidden
/// inside a For each, Try, Look at, Test or Check body would have to suspend
/// a nested execution, so such a body takes the collect-all path instead.
pub fn gen_resume_safe(b: &FnBody) -> bool {
    match b {
        FnBody::Expr(_) => true, // nothing to suspend; the body finishes at once
        FnBody::Block(stmts) => hand_flat_ok(stmts),
    }
}

fn hand_flat_ok(stmts: &[Stmt]) -> bool {
    stmts.iter().all(|st| match st {
        Stmt::HandBack(_) => true,
        Stmt::If { branches, other } => {
            branches.iter().all(|(_, b)| hand_flat_ok(b))
                && other.as_ref().map_or(true, |o| hand_flat_ok(o))
        }
        Stmt::RepeatTimes { body, .. } | Stmt::RepeatForever { body } => hand_flat_ok(body),
        Stmt::RepeatWhile { body, .. } | Stmt::ForRange { body, .. } => hand_flat_ok(body),
        // delegated statements must not hide a Hand back in their bodies
        Stmt::ForIn { body, .. } => no_nested_hand(body),
        Stmt::Try {
            sentence,
            success,
            failure,
        } => {
            one_no_hand(sentence)
                && no_nested_hand(success)
                && failure.iter().all(|(_, b)| no_nested_hand(b))
        }
        Stmt::Test { body, .. } | Stmt::Check { body, .. } => no_nested_hand(body),
        Stmt::LookAt { whens, .. } => whens.iter().all(|w| no_nested_hand(&w.body)),
        _ => true,
    })
}

fn no_nested_hand(stmts: &[Stmt]) -> bool {
    stmts.iter().all(one_no_hand)
}

fn one_no_hand(st: &Stmt) -> bool {
    match st {
        Stmt::HandBack(_) => false,
        Stmt::If { branches, other } => {
            branches.iter().all(|(_, b)| no_nested_hand(b))
                && other.as_ref().map_or(true, |o| no_nested_hand(o))
        }
        Stmt::RepeatTimes { body, .. } | Stmt::RepeatForever { body } => no_nested_hand(body),
        Stmt::RepeatWhile { body, .. } | Stmt::ForRange { body, .. } => no_nested_hand(body),
        Stmt::ForIn { body, .. } => no_nested_hand(body),
        Stmt::Try {
            sentence,
            success,
            failure,
        } => {
            one_no_hand(sentence)
                && no_nested_hand(success)
                && failure.iter().all(|(_, b)| no_nested_hand(b))
        }
        Stmt::Test { body, .. } | Stmt::Check { body, .. } => no_nested_hand(body),
        Stmt::LookAt { whens, .. } => whens.iter().all(|w| no_nested_hand(&w.body)),
        _ => true,
    }
}

// ---------------------------------------------------------------- shapes

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Op {
    Plus,
    Minus,
    Time,
    DividedBy,      // gives a decimal
    WholeDividedBy, // drops the part after the point, toward zero
    Remainder,
    Power,
    // checked / wrapping / saturating whole math (ch.19, M2-S24):
    CheckedPlus,
    CheckedMinus,
    CheckedTimes,
    WrappingPlus,
    WrappingMinus,
    WrappingTimes,
    SaturatingPlus,
    SaturatingMinus,
    SaturatingTimes,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Rel {
    Equal,
    Not,
    More,
    Less,
    AtLeast,
    AtMost,
    Close,
    Between,
    IsEmpty, // coll is empty
    Has,     // coll has item
    Missing, // x is missing (maybe, ch.18)
    There,   // x is there (= not missing, ch.18)
}

#[derive(Clone, Debug)]
pub struct Comp {
    pub negate: bool,
    pub rel: Rel,
    pub l: Box<Expr>,
    pub r: Vec<Box<Expr>>, // one, or two for between A and B
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: Kind,
    pub e: E,
    pub dis: String,    // display text, used by the T0302 Fix line
    pub can_fail: bool, // a text-to-number conversion
    pub num_word: bool, // a spelled number word in a value position
}

#[derive(Clone, Debug)]
pub enum E {
    Whole(i64),
    Dec(f64),
    Boolean(bool),
    Missing,
    Word(String), // original-case text word or number word
    Name(String), // lowercase spelling
    Neg(Box<Expr>),
    Binary {
        op: Op,
        l: Box<Expr>,
        r: Box<Expr>,
    },
    DivWhole(Box<Expr>, Box<Expr>), // A whole divided by B
    Rem(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, Box<Expr>),
    Round(Box<Expr>, bool),
    Factorial(Box<Expr>),
    Call {
        name: String,
        args: Vec<Expr>,
    },
    CountIn(Box<Expr>),                // how many in X (text -> whole)
    Lower(Box<Expr>),                  // lower of X (text -> text)
    AndOr(Box<Expr>, Box<Expr>, bool), // true = and
    AsWhole(Box<Expr>),
    AsDecimal(Box<Expr>),
    AsBig(Box<Expr>),
    AsText(Box<Expr>),
    AsNumber(Box<Expr>), // text -> number, can fail
    AsMaybe(Box<Expr>),  // a value in maybe kind (ch.18)
    It,
    Them,
    ListOf(Vec<Expr>),            // list of A and B and C
    PairOf(Box<Expr>, Box<Expr>), // pair of A and B
    FirstOf(Box<Expr>),           // first of X
    SecondOf(Box<Expr>),          // second of X
    Combine {
        list: Box<Expr>,
        word: String,
    }, // Combine L with plus. -> value
    ApplyEach {
        name: String,
        list: Box<Expr>,
    }, // Apply f to each of L. -> list
    Sorted(Box<Expr>, bool),      // X sorted [descending]. (Ch.8)
    Reverse(Box<Expr>),           // X reversed. (Ch.11)
    Unique(Box<Expr>),            // X unique. (Ch.11)
    Fallback {
        value: Box<Expr>,
        default: Box<Expr>,
    }, // X fallback Y (Ch.18)
    JoinedWith(Box<Expr>, String), // X joined with word -> text
    Upper(Box<Expr>),             // upper of text (ch.14)
    Trimmed(Box<Expr>),           // text trimmed (ch.14)
    Normalized(Box<Expr>),        // text normalized (ch.14)
    PatWords {
        parts: Vec<Pat>,
    }, // a text pattern (ch.14, M2-G30)
    RecordOf {
        type_name: String,
        parts: Vec<(String, Expr)>,
    }, // a person with name Maya and age 31 (ch.20)
    EnumOf {
        shape: String,
        parts: Vec<(String, Expr)>,
    }, // card with owner Maya / red (ch.21)
    PartOf {
        type_name: String,
        part: String,
        base: Box<Expr>,
    }, // age of maya (ch.20)
    CopyOf(Box<Expr>),            // copy of X (ch.20)
    Move(Box<Expr>),              // give X (ch.28)
    Share(Box<Expr>),             // share X (ch.28)
    WeakShare(Box<Expr>),         // weak share X (ch.28)
    /// channel of T [holding N] (M4-G7): a new channel value.
    ChannelOf {
        item: Kind,
        cap: usize,
    },
    /// guarded V (M4-G8): a new guarded value holding V.
    GuardedOf(Box<Expr>),
    /// atomic number (M4-G9): a new atomic number value, starting at 0.
    AtomicNum,
    /// counter (M4-G10): a new counter value, starting at 0.
    CounterZero,
    /// file F exists (M4-G45): a yes-or-no question about a path.
    FileExists(FileRef),
    /// M4-6 (Appendix K S46): json of x - the compact json text of a
    /// value (no spaces).
    JsonOf(Box<Expr>),
    /// M4-10 (Appendix K G77): one row of the request reads, evaluated
    /// against the ambient handler context (method/page/text/data/
    /// header NAME/query NAME/parameter NAME of request).
    RequestRead {
        row: RequestRow,
    },
    // ---- M4-7 (Appendix K 7.7) time, random, secrets ----
    /// date N and N and N (M4-G54): a literal calendar day in the
    /// proleptic Gregorian calendar. Validated at compile time
    /// (impossible date is T0620).
    DateCtor {
        y: i64,
        m: i64,
        d: i64,
    },
    /// today (M4-G54): the date in the local zone.
    Today,
    /// now (M4-G55): the instant in the local zone.
    Now,
    /// moment of D at H and M (M4-G55): H:M:00 on date D in the local
    /// zone (the compile check holds H < 24 and M < 60, T0620 family).
    MomentAt {
        date: Box<Expr>,
        h: i64,
        m: i64,
    },
    /// M in zone <names> (M4-G55): the same instant in another IANA
    /// zone; the name is matched ignoring case, spaces and slashes
    /// (T0171 when no zone matches).
    InZone {
        base: Box<Expr>,
        zone: String,
    },
    /// N <unit> after/before X (M4-G56): calendar rules for dates (days)
    /// and exact seconds for moments. Months and years are not units.
    TimeShift {
        n: i64,
        unit: String,
        before: bool,
        base: Box<Expr>,
    },
    /// M4-S52/G5: a duration value, NUMBER time_unit such as 5 seconds
    /// (units: milliseconds, seconds, minutes, hours, days, weeks).
    /// Nanoseconds, signed.
    DurationOf {
        nanos: i128,
    },
    /// days between X and Y (M4-G56): calendar days between two dates.
    DaysBetween {
        a: Box<Expr>,
        b: Box<Expr>,
    },
    /// seconds between X and Y (M4-G56): exact seconds between two
    /// moments.
    SecondsBetween {
        a: Box<Expr>,
        b: Box<Expr>,
    },
    /// random number from A to B (M4-G57): uniform over both ends, from
    /// the program's generator (xoshiro256++ seeded by splitmix64).
    RandomRange {
        a: Box<Expr>,
        b: Box<Expr>,
    },
    /// random decimal (M4-G57): [0, 1) from the program's generator.
    RandomDec,
    /// random item of L (M4-G57).
    RandomItem {
        list: Box<Expr>,
    },
    /// L shuffled (M4-G57): the Fisher-Yates method.
    Shuffled {
        list: Box<Expr>,
    },
    /// hash of X (M4-G59): the SHA-256 of the UTF-8 bytes of the text
    /// (or of a list of whole numbers 0..255), as 64 lower-case hex
    /// digits.
    HashOf(Box<Expr>),
    /// secret X (M4-G60): the value becomes a secret (prints hidden,
    /// never logged, cannot be compared or converted, zeroed when
    /// dropped).
    SecretOf(Box<Expr>),
    /// reveal X (M4-G61): the text (or bytes) of a secret.
    Reveal(Box<Expr>),
    /// Environment <names> (M4-G24): the environment variable named by
    /// the name's words in upper case joined by _ (Lykaon_MODE). It gives
    /// maybe text (M4-S80); the compile check requires the name's words
    /// to spell a valid variable name (letters, digits, _ after the
    /// first letter of each word).
    Environment {
        name: String,
    },
    /// Read input (M4-G27): all of standard input as text (M4-S85).
    ReadInput,
    CollEmpty {
        kind: Kind,
        size: Option<usize>,
    }, // empty collection of a kind (M2)
    ItemN {
        list: Box<Expr>,
        n: Box<Expr>,
    }, // item N of list (T0601 if out of range)
    SafeItemN {
        list: Box<Expr>,
        n: Box<Expr>,
    }, // safe item N of list (maybe T)
    ItemsRange {
        list: Box<Expr>,
        from: Box<Expr>,
        to: Box<Expr>,
    }, // items A to B of list
    FirstN {
        list: Box<Expr>,
        n: Box<Expr>,
    }, // first N of list
    /// list where cond keeps the items for which cond is yes (ch.24, M3-S24).
    /// In cond, it is the item.
    Where {
        list: Box<Expr>,
        cond: Box<Expr>,
    },
    /// first N fibonacci (ch.25, M3-D12): the built-in lazy sequence 0, 1, 1, 2...
    FirstFib(Box<Expr>),
    /// primes to N (M3-D12): the built-in sequence of primes up to N.
    PrimesTo(Box<Expr>),
    /// rex as any speaker (ch.23, M3-S18): convert a kind that keeps the
    /// interface promise to its dynamic kind.
    AsDyn {
        value: Box<Expr>,
        verb: String,
    },
    /// a function name in a value position where a function is expected
    /// (M3-S21): Apply f to each of, Combine list with f, an input of kind
    /// function from A to B.
    FnRef(String),
    /// biggest of X and Y and ... / smallest of ... (ch.8, M3-D15): an
    /// inline list of ordered values.
    MinMax {
        big: bool,
        items: Vec<Expr>,
    },
    LastOf(Box<Expr>), // last of list (maybe T)
    PositionOf {
        haystack: Box<Expr>,
        needle: Box<Expr>,
    }, // position of x in list/text (maybe whole)
    ValueOf {
        map: Box<Expr>,
        key: Box<Expr>,
    }, // value of k in map (maybe V)
    IsEmpty(Box<Expr>), // coll is empty (yes/no)
    Has {
        coll: Box<Expr>,
        item: Box<Expr>,
    }, // coll has x (yes/no)
    Union {
        a: Box<Expr>,
        b: Box<Expr>,
    }, // union of sets
    Overlap {
        a: Box<Expr>,
        b: Box<Expr>,
    }, // overlap of sets
    Difference {
        a: Box<Expr>,
        b: Box<Expr>,
    }, // difference of sets
    Split {
        text: Box<Expr>,
        sep: Box<Expr>,
    }, // split text at sep (list of text)
    Replace {
        pat: Box<Expr>,
        repl: Box<Expr>,
        text: Box<Expr>,
    }, // replace P with y in text
    Flat(Vec<Expr>),   // a run of Say words joined with spaces
    Compare(Comp),
}

#[derive(Clone, Debug, Default)]
pub struct SayMods {
    pub places: Option<usize>,
    pub width: Option<usize>,
    pub without_newline: bool,
    pub literally: bool,
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub name: String,
    pub mutable: bool,
    pub is_const: bool,
    pub expr: Expr,
    pub fallback: Option<Expr>, // If that fails use X.
    pub shared: bool,           // Share <name>. (ch.36)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AskKind {
    Text,
    Number,
    Decimal,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Note,
    Define(Decl),
    Set {
        name: String,
        expr: Expr,
    },
    Say {
        expr: Expr,
        mods: SayMods,
        lines: Vec<String>,
    },
    Ask {
        name: String,
        kind: AskKind,
        fallback: Option<Expr>,
    },
    If {
        branches: Vec<(Expr, Vec<Stmt>)>,
        other: Option<Vec<Stmt>>,
    },
    RepeatTimes {
        count: Expr,
        body: Vec<Stmt>,
    },
    RepeatForever {
        body: Vec<Stmt>,
    },
    RepeatWhile {
        cond: Expr,
        body: Vec<Stmt>,
    },
    ForRange {
        var: String,
        from: Expr,
        to: Expr,
        body: Vec<Stmt>,
    },
    ForIn {
        vars: Vec<String>,
        list: Expr,
        body: Vec<Stmt>,
    },
    Evaluate {
        expr: Expr,
        list: bool,
    }, // Combine / Apply: the sentence gives a result (it / them)
    Append {
        value: Expr,
        list: String,
    }, // Add v to the name.
    Put {
        map: String,
        key: Option<Expr>,
        value: Expr,
    }, // Put v in map under k. / Put v in set. (M2)
    Remove {
        coll: String,
        value: Expr,
    }, // Remove x from coll. (M2)
    RemoveFirst {
        coll: String,
    }, // Remove first from queue. (M2)
    SetPart {
        path: Vec<String>,
        expr: Expr,
    }, // Set age of maya to 32. (ch.20)
    LookAt {
        value: Expr,
        whens: Vec<When>,
    }, // Look at / When (ch.21)
    DefineEnum {
        name: String,
        variants: Vec<(String, Vec<(String, Kind)>)>,
    }, // A payment is cash or card with owner. (ch.21)
    // can fail / Try / Fail (ch.19, M2)
    Try {
        sentence: Box<Stmt>,
        success: Vec<Stmt>,
        failure: Vec<(Option<String>, Vec<Stmt>)>,
    },
    Fail {
        message: Expr,
    }, // Fail with TEXT (only inside a can fail function)
    PassFailureUp, // Pass failure up. (only inside a can fail function)
    Close {
        name: String,
    }, // Close x. (ch.31, can fail)
    // Modules (ch.36)
    Share {
        name: String,
    }, // Share <name>. (make a definition visible to other modules)
    Use {
        file: String,
    }, // Use <file>. (bring another module's shared names in)
    // Tests (ch.38)
    Test {
        name: String,
        body: Vec<Stmt>,
    }, // Test <name>. block
    Check {
        text: String,
        cond: Option<Expr>,
        must_fail: bool,
        prop: Option<(String, String)>,
        body: Vec<Stmt>,
    }, // Check that cond. / Check that this fails. / Check for any <kind> <name>. (ch.38)
    Pretend {
        name: String,
        value: Expr,
    }, // Pretend f gives V.
    Stop,
    Skip,
    GiveBack(Option<Expr>),
    /// Hand back <value>. inside a generator function (ch.25, M3-S30).
    HandBack(Expr),
    /// A local function definition inside a block: a closure (ch.24, M3-D2).
    DefineLocalFn(FuncDef),
    // ---- M4 (Appendix K): tasks, channels, timers ----
    /// Start task NAME. + block: run the block as a task and go on (M4-G1).
    /// The task gives a value with Give back EXPR. as its last sentence
    /// (M4-S3); a task with no Give back gives nothing.
    StartTask {
        name: String,
        body: Vec<Stmt>,
    },
    /// Wait for NAME.: pause until the task ends; the result is taken once
    /// (M4-S4). Waiting on a name that is not a task is T0168.
    WaitFor {
        name: String,
    },
    /// Do these together. + block: run the block, then wait for every task
    /// started inside it (at any depth) (M4-S5). The block is transparent
    /// for task names (M4-D2).
    DoTogether {
        body: Vec<Stmt>,
    },
    /// Stop task NAME.: send the cancel request; does not wait (M4-S7).
    StopTask {
        name: String,
    },
    /// Sleep for N <unit>.: pause; cancellable (M4-S9, M4-G4/G5/G6).
    SleepFor {
        amount: u64,
        unit: String,
    },
    /// Send VALUE to CHANNELNAME. (M4-G11): put a value on the channel.
    /// Send pauses when the channel is full (M4-S11); a Send on a closed
    /// channel stops the program (T0609).
    Send {
        value: Expr,
        name: String,
    },
    /// Receive from CHANNELNAME. (M4-G12): take the oldest item off the
    /// channel; the value is it (M4-S13). Receive pauses when the channel
    /// is empty; when the channel is closed and empty the value is missing.
    Receive {
        name: String,
    },
    /// Add VALUE to NAME atomically. (M4-G13): one machine step, sequentially
    /// consistent (M4-S19). A counter's plain `Add V to NAME.` lands here
    /// too when the target name was declared a counter (M4-S20).
    AtomicAdd {
        value: Expr,
        name: String,
    },
    /// After N <unit>. + block (M4-G14): a one-shot timer task. It goes on
    /// and the block runs once (M4-S25); a never-fired timer fires when
    /// its scope would end (see deviations for the eager calendar).
    AfterTimer {
        amount: u64,
        unit: String,
        body: Vec<Stmt>,
    },
    /// Every N <unit>. + block (M4-G15): a repeating timer with fixed-rate,
    /// never-overlapping rounds (M4-D12). Stop. inside a round ends it;
    /// cancelled when the enclosing scope ends (M4-S26).
    EveryTimer {
        amount: u64,
        unit: String,
        body: Vec<Stmt>,
    },
    /// For each x as they arrive from CHANNEL. + block (M4-G16): loops over
    /// Receive from the channel until it closes; in the block x and it are
    /// the received value; Stop. leaves the loop (M4-S27).
    StreamLoop {
        var: String,
        channel: String,
        body: Vec<Stmt>,
    },
    /// Use N workers. (M4-G17): sets the worker count for Spread sentences
    /// that follow, in this and inner blocks; 1..=256 (M4-S22).
    UseWorkers {
        count: u64,
    },
    /// Spread each of ITEMS over workers. + block (M4-G18): the block runs
    /// once per item (it is the item, M4-S23); the block's result is its
    /// Give back, and the results are collected in item order into them.
    /// A failure inside stops the other workers; the sentence is can fail
    /// (T0311 if unhandled) (M4-S24).
    Spread {
        items: Expr,
        body: Vec<Stmt>,
    },

    // ---- M4 (Appendix K 7.5) files, paths, watching, zip ----
    /// Read file F. (M4-G34): the whole text into it (M4-S36).
    ReadFile {
        file: FileRef,
    },
    /// Read bytes of file F. (M4-G35): the bytes as a list of whole
    /// numbers into it.
    ReadBytes {
        file: FileRef,
    },
    /// Write X to file F. (M4-G36): fails if the file exists (M4-S34);
    /// a text or a list of text is written as lines (M4-S35).
    WriteFile {
        file: FileRef,
        value: Expr,
    },
    /// Append X to file F. (M4-G37): creates the file if needed.
    AppendFile {
        file: FileRef,
        value: Expr,
    },
    /// Replace file F with X. (M4-G38): creates or overwrites, atomically.
    ReplaceFile {
        file: FileRef,
        value: Expr,
    },
    /// For each NAME in file F. + block (M4-G39): the lines without
    /// their line endings, streaming.
    ForEachLine {
        var: String,
        file: FileRef,
        body: Vec<Stmt>,
    },
    /// Make folder F. (M4-G40): makes the folder and the parent folders.
    MakeFolder {
        file: FileRef,
    },
    /// Remove file F. / Remove folder F. (M4-G41).
    RemovePath {
        file: FileRef,
    },
    /// Move F to F2. (M4-G42).
    MovePath {
        from: FileRef,
        to: FileRef,
    },
    /// Duplicate F as F2. (M4-G43).
    DuplicatePath {
        from: FileRef,
        to: FileRef,
    },
    /// List files in folder F. (M4-G44): the entry names (sorted) into it.
    ListFolder {
        file: FileRef,
    },
    /// Make temporary file NAME. (M4-G46): the path of a new empty temp
    /// file bound to NAME; the file is removed when the block that holds
    /// it ends, even after a failure (M4-S38).
    MakeTempFile {
        name: String,
    },
    /// When file F changes. + block (M4-G47): the block runs once per
    /// change event (create, write, rename, delete), merged when closer
    /// than 100 ms; the block is a task in the enclosing scope (M4-S39).
    WhenFileChanges {
        file: FileRef,
        body: Vec<Stmt>,
    },
    /// Zip folder to file / Unzip file to folder / Gzip file to file
    /// (M4-G48; M4-S41: sorted entries, fixed 1980 stamp, deflate).
    ZipOp {
        op: ZipKind,
        from: FileRef,
        to: FileRef,
    },
    /// M4-6 (Appendix K 7.6): Read json file F as T. (and toml, yaml,
    /// xml, csv): the decoded value lands in the fresh result (it).
    /// The target kind was checked at compile time (a record, enum,
    /// list, map of text, maybe or base kind - a csv target is a list,
    /// M4-S47).
    ReadFormat {
        format: String,
        file: FileRef,
        target: Kind,
    },
    /// M4-6: Read json from text as T.: the decode source is a text
    /// value instead of a file.
    ReadFormatText {
        format: String,
        value: Expr,
        target: Kind,
    },
    /// M4-6: Save x as json to file F. (the format word is also toml,
    /// yaml, xml, csv): the encoded text of the value is written (the
    /// json encoding is pretty with two spaces of indentation and the
    /// line feed at the end, M4-S46).
    SaveFormat {
        value: Expr,
        format: String,
        file: FileRef,
    },
    /// M4-7 (Appendix K S54, M4-G58): Use seed N. sets the program's
    /// random generator (xoshiro256++ seeded by splitmix64 from N) for
    /// the rest of the run. A run without Use seed uses the operating
    /// system's entropy; tests use seed 42 unless a program sets
    /// another.
    UseSeed {
        seed: u64,
    },

    // ---- M4-8 (Appendix K 7.10 system, 7.11 command-line tools) ----
    /// Run NAME [with operand (and operand)*]. (M4-G20): starts the program
    /// found on the path (T0171 when the name carries a path), one argument
    /// per operand, no shell (M4-S76). The child's standard output is the
    /// fresh result (it, M4-D16); a child exit status other than 0 fails
    /// with kind other, the message being the child's error text.
    RunProc {
        name: String,
        args: Vec<Expr>,
    },
    /// Exit with NUMBER. (M4-G21): ends the program with that code (0..255,
    /// checked at compile time, M4-S78). The active cleanups run first
    /// (M4-S77), then the process ends with that code.
    Exit {
        code: i64,
    },
    /// When signal stop|interrupt|hangup arrives. + block (M4-G22/G23):
    /// registers the block for that signal (M4-S79). The signal is polled
    /// at the pause points; the block runs as a task when it arrives;
    /// without a block the program ends after cleaning up (interrupt 130,
    /// stop 143, hangup 129).
    WhenSignal {
        signal: SignalName,
        body: Vec<Stmt>,
    },
    /// For each NAME in input. + block (M4-G27): the lines of standard
    /// input (buffered first, M4-S85) one at a time, without the line
    /// endings. Stop. leaves the loop.
    ForEachInput {
        var: String,
        body: Vec<Stmt>,
    },
    // ---- M4-9 (Appendix K 7.12 logging and settings) ----
    /// Log LEVEL TEXT. (M4-G28): writes LEVEL TEXT and a line feed to
    /// standard error (M4-D11) when the run's log level admits it. The
    /// text is raw text; names in it are replaced as in Say (a secret
    /// writes hidden, M4-S89; a counter shows its value, M4-S90). The
    /// text fields are exactly a Say's (the sentence is parsed with the
    /// Say machinery); the line feed is always written (M4-S87).
    Log {
        level: LogLevel,
        expr: Expr,
        mods: SayMods,
        lines: Vec<String>,
    },
    /// Use log level LEVEL. (M4-S88): sets the run's log level. The
    /// order is debug < info < warning < error; the default is info, so
    /// debug lines are not written until this sentence says otherwise.
    LogLevel {
        level: LogLevel,
    },

    // ---- M4-10 (Appendix K 7.8 network) ----
    /// Fetch ADDRESS [using METHOD] [with data E] [with header WORDS E]*
    /// [with query WORDS E]* [without checking certificates.]
    /// (M4-G67/G68). Sends the request; the fresh result is the response
    /// record: status (whole), body (text), headers (map of text to
    /// text). A status of 400 or more is NOT a failure (M4-S60); the
    /// connection-level failures are the ordinary anonymous failure in
    /// this cut (the M4-5 file posture, logged).
    Fetch {
        method: NetMethod,
        address: NetAddress,
        data: Option<Expr>,
        headers: Vec<(String, Expr)>,
        query: Vec<(String, Expr)>,
        /// S62: skip the certificate check (inside Be careful only).
        skip_tls: bool,
    },
    /// Post DATA to ADDRESS. (M4-G70): Fetch ADDRESS using post with
    /// data DATA (M4-S60).
    PostTo {
        data: Expr,
        address: NetAddress,
    },

    /// Serve [securely] on port N. [using certificate F and key F.]
    /// + block (M4-G71/G72): listens on all addresses (M4-S64); the
    /// block's ordinary sentences run once at start, then the When
    /// someone / When live blocks serve until the program ends or Exit.
    Serve {
        port: u16,
        secure: bool,
        cert: Option<FileRef>,
        key: Option<FileRef>,
        body: Vec<Stmt>,
    },
    /// When someone gets|posts|puts|deletes|patches PAGE. + block
    /// (M4-G73/G74): one request handler. The body runs per matching
    /// request with request and session provided (M4-S68); Respond
    /// answers (M4-S69).
    WhenSomeone {
        method: NetMethod,
        page: String,
        pattern: Vec<PageSeg>,
        body: Vec<Stmt>,
    },
    /// When someone opens live PAGE. + block (M4-G75): a WebSocket
    /// handler; connection is provided (M4-S73).
    WhenLive {
        page: String,
        pattern: Vec<PageSeg>,
        body: Vec<Stmt>,
    },
    /// Respond with ... (M4-G76): answers the current request. The
    /// first Respond on the path answers; the compile checks are
    /// T0166 (no Respond) and T0168 (two Responds).
    Respond {
        kind: RespondKind,
    },
    /// Page NAMES is SEGMENTS. (M4-G78/G79/G80): a page table row; the
    /// name is looked up by addresses and When someone sentences.
    PageDecl {
        name: String,
        segments: Vec<PageSeg>,
    },
    /// Send X to connection. inside a live block (M4-S73): one text
    /// frame (the shown wording of X).
    WsSend {
        value: Expr,
    },
    /// Receive from connection. inside a live block (M4-S73): maybe
    /// text; missing when the other side closed. The fresh result.
    WsRecv,

    /// Be careful. + block (S62): the dangerous sentences run only
    /// here (the TLS-skip Fetch). The body runs inline.
    Careful {
        body: Vec<Stmt>,
    },
}

/// A page path segment (M4-G80): a literal lower-case word (several
/// words joined by -) or "anything called NAME" (the {id} parameter).
#[derive(Clone, Debug)]
pub enum PageSeg {
    Lit(String),
    Param(String),
}

/// The Respond variants (M4-G76/S69).
#[derive(Clone, Debug)]
pub enum RespondKind {
    /// Respond with TEXT. - status 200, text/plain; charset=utf-8.
    Text(Expr),
    /// Respond with json X. - 200, application/json, body json of X.
    Json(Expr),
    /// Respond with status N. / Respond with status N and TEXT.
    Status(i64, Option<Expr>),
    /// Respond with template NAME. - the file NAME.template in the
    /// source folder; {name} filled and HTML-made-safe, {raw name} not.
    Template(String),
    /// Respond with literally TEXT. - the text even when it starts
    /// with json, status, template or literally.
    Literally(Expr),
}

/// The request read rows (M4-G77), read from the ambient handler
/// context: method/page of request are text; text of request is the
/// body as text; data of request the body as bytes; header/query/
/// parameter NAME of request are maybe text (missing when absent).
#[derive(Clone, Debug)]
pub enum RequestRow {
    Method,
    Page,
    Text,
    Data,
    Header(String),
    Query(String),
    Parameter(String),
}

/// An address (M4-G62..G66), resolved at compile time: the scheme
/// (secure = https, the default; plain = http), the host words joined by
/// dot (M4-S58), the optional port (443/80 defaults) and the place as a
/// path (a page name looked up in the Page table, or "path a and b"
/// segments joined with "/").
#[derive(Clone, Debug)]
pub struct NetAddress {
    pub secure: bool,
    pub host: String,
    pub port: u16,
    pub path: String,
}

/// The method word (M4-G69). GET is the default (M4-S60).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NetMethod {
    Get,
    Post,
    Put,
    Delete,
    Patch,
}

impl NetMethod {
    pub fn wire(self) -> &'static str {
        match self {
            NetMethod::Get => "GET",
            NetMethod::Post => "POST",
            NetMethod::Put => "PUT",
            NetMethod::Delete => "DELETE",
            NetMethod::Patch => "PATCH",
        }
    }

    pub fn from_word(w: &str) -> Option<NetMethod> {
        match w {
            "get" => Some(NetMethod::Get),
            "post" => Some(NetMethod::Post),
            "put" => Some(NetMethod::Put),
            "delete" => Some(NetMethod::Delete),
            "patch" => Some(NetMethod::Patch),
            _ => None,
        }
    }
}

/// The response record's compile kind (M4-S60): status (whole), body
/// (text), headers (map of text to text). `it` after a Fetch carries
/// this kind, so `status of it.` reads as a part read.
pub fn response_kind() -> Kind {
    Kind::Record(
        "response".to_string(),
        vec![
            ("status".to_string(), Kind::Whole),
            ("body".to_string(), Kind::Text),
            (
                "headers".to_string(),
                Kind::Map(Box::new(Kind::Text), Box::new(Kind::Text)),
            ),
        ],
    )
}

/// M4-S88: the log levels, in order from the least to the most severe.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogLevel {
    Debug,
    Info,
    Warning,
    Error,
}

impl LogLevel {
    /// The word in the sentence (S87/S88).
    pub fn word(self) -> &'static str {
        match self {
            LogLevel::Debug => "debug",
            LogLevel::Info => "info",
            LogLevel::Warning => "warning",
            LogLevel::Error => "error",
        }
    }

    /// The rank for the level comparison (S88): a Log line is written
    /// when its level's rank is at or above the run's level rank.
    pub fn rank(self) -> u8 {
        match self {
            LogLevel::Debug => 0,
            LogLevel::Info => 1,
            LogLevel::Warning => 2,
            LogLevel::Error => 3,
        }
    }

    pub fn from_word(w: &str) -> Option<LogLevel> {
        match w {
            "debug" => Some(LogLevel::Debug),
            "info" => Some(LogLevel::Info),
            "warning" => Some(LogLevel::Warning),
            "error" => Some(LogLevel::Error),
            _ => None,
        }
    }
}

/// M4-G23: the signals a program can wait for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignalName {
    Stop,
    Interrupt,
    Hangup,
}

impl SignalName {
    /// The environment-independent display word.
    pub fn word(self) -> &'static str {
        match self {
            SignalName::Stop => "stop",
            SignalName::Interrupt => "interrupt",
            SignalName::Hangup => "hangup",
        }
    }

    /// The exit code when the signal arrives with no block registered
    /// (M4-S79): 128 + the signal number convention (interrupt = SIGINT 2,
    /// stop = SIGTERM 15, hangup = SIGHUP 1). The spec's sentence lists the
    /// codes in the reverse order; the 128+n convention is what it
    /// references (logged in LYKAON_DEVIATIONS.md).
    pub fn default_exit(self) -> i64 {
        match self {
            SignalName::Interrupt => 130,
            SignalName::Stop => 143,
            SignalName::Hangup => 129,
        }
    }
}

/// M4-G25: Takes NAME as [maybe] T. - one positional command-line
/// argument. The name keeps the words as written (lower-case, joined by
/// one space for display); the value is seeded into the program before the
/// body runs. A required (non-maybe) argument that is absent makes the
/// tool print the usage text and exit 2 (M4-S83).
#[derive(Clone, Debug)]
pub struct ToolArg {
    pub name: String, // display name: the words joined by one space
    pub kind: ToolKind,
    pub maybe: bool,
}

/// M4-G26: Option NAME is [maybe] T [defaulting to V]. - a flag with a
/// value: --name value or --name=value (S82), the flag spelling joining
/// the name's words with -. The default is a literal value of the option's
/// kind (a non-literal default is refused at compile time - logged).
#[derive(Clone, Debug)]
pub struct ToolOpt {
    pub name: String,
    pub kind: ToolKind,
    pub maybe: bool,
    pub default: Option<Value>,
}

impl ToolOpt {
    /// The command-line spelling of the option: the words joined by -
    /// (S82), lower case.
    pub fn flag(&self) -> String {
        self.name.replace(' ', "-")
    }
}

/// The kinds a command line can spell (M4-G25/G26): the number kinds and
/// text, optionally wrapped in maybe. `number` is the language's general
/// number: a value that looks whole reads as a whole number, else as a
/// decimal (M3-S10's per-instance check, applied at parse time).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ToolKind {
    Whole,
    Number,
    Decimal,
    Text,
}

impl ToolKind {
    /// The display spelling in the usage text (M4-S83).
    pub fn word(self) -> &'static str {
        match self {
            ToolKind::Whole => "whole number",
            ToolKind::Number => "number",
            ToolKind::Decimal => "decimal",
            ToolKind::Text => "text",
        }
    }

    /// Parse one command-line word into a value of this kind. None = wrong
    /// kind (the tool prints the usage text and exits 2, M4-S83). A bare
    /// flag (no value, S82's --verbose) reads as 1 for the number kinds
    /// and the text "on" for text (logged).
    pub fn parse_word(self, w: &str) -> Option<Value> {
        match self {
            ToolKind::Whole => w.parse::<i64>().ok().map(Value::Whole),
            ToolKind::Number => {
                if let Ok(n) = w.parse::<i64>() {
                    Some(Value::Whole(n))
                } else {
                    w.parse::<f64>().ok().map(Value::Dec)
                }
            }
            ToolKind::Decimal => w.parse::<f64>().ok().map(Value::Dec),
            ToolKind::Text => Some(Value::Text(w.to_string())),
        }
    }

    /// The value a bare flag (no value after the name, S82) stands for.
    pub fn bare_flag(self) -> Value {
        match self {
            ToolKind::Whole | ToolKind::Number | ToolKind::Decimal => Value::Whole(1),
            ToolKind::Text => Value::Text("on".to_string()),
        }
    }
}

/// M4-G48 zip/gzip/unzip sentence kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZipKind {
    Zip,
    Unzip,
    Gzip,
}

/// M4-G32 path roots: the start a file or folder reference is built from.
#[derive(Clone, Debug, PartialEq)]
pub enum FileRoot {
    Parent,
    Home,
    Current,
    Temporary,
    Root,
    Drive(String),
}

/// M4-G28 file_ref / M4-G33 folder_ref (the same resolved shape; `folder`
/// marks what was written as a folder reference). The words of a name are
/// the file's name; folder steps nest outward (M4-S31: the first named
/// folder is closest to the file), `ext` is with-extension (M4-S32) and
/// `root` is the optional root words (M4-S30).
#[derive(Clone, Debug, PartialEq)]
pub struct FileRef {
    pub folder: bool,
    /// file named TEXT (M4-S29): a raw path, terminal per the grammar.
    pub raw: Option<String>,
    /// a name bound by Make temporary file NAME (the binding wins).
    pub temp: Option<String>,
    /// the NAME words of the file (lowercased).
    pub name: String,
    pub ext: Option<String>,
    /// folder steps in text order (innermost first);
    /// resolution joins them in reverse.
    pub folders: Vec<String>,
    pub root: Option<FileRoot>,
}

/// A Requires or Ensures contract (ch.64). `checked` keeps it in fast
/// builds (M3-S37). The text is used by the T0602 message.
#[derive(Clone, Debug)]
pub struct Contract {
    pub cond: Expr,
    pub checked: bool,
    pub is_ensures: bool,
    pub line: usize,
    pub text: String,
}

/// The agent noun of a verb: speak -> speaker (M3-D11).
pub fn agent_noun(verb: &str) -> String {
    if verb.ends_with('e') {
        format!("{}r", &verb[..verb.len() - 1])
    } else {
        format!("{verb}er")
    }
}

#[derive(Clone, Debug)]
pub struct When {
    pub shape: String,      // the variant word (card)
    pub names: Vec<String>, // fresh names for the parts, in declared order
    pub body: Vec<Stmt>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub name: String,
    pub inputs: Vec<(String, ParamMode)>,
    pub can_fail: bool,
    pub default_last: Option<Expr>, // defaulting to <value> (Ch.15)
    pub body: FnBody,
    pub shared: bool, // Share <name>. (ch.36)
    // ---- M3 ----
    /// Stated kinds of the inputs, parallel to `inputs` where present
    /// (M3-G2). None = generic (M3-S8).
    pub input_types: Vec<Option<ParamType>>,
    /// The stated kind of the given value: `give ... as number` (M3-G19).
    pub result_type: Option<ParamType>,
    /// Requires contracts, then Ensures (ch.64); stand first in the block.
    pub requires: Vec<Contract>,
    pub ensures: Vec<Contract>,
    /// Tags before the definition (M3-S39): test, deprecated, slow.
    pub tags: Vec<String>,
    /// The body contains Hand back: the function is a generator (M3-S30).
    pub is_generator: bool,
    /// Written with To inside a block: a local function and closure (M3-D2).
    pub is_local: bool,
    /// Names of fixed top-level values visible where the function is written,
    /// excluding its own inputs: captured by shared borrow and seeded into the
    /// call frame (ch.24, M3-D2; also used for top-level functions so they can
    /// see fixed names defined above them in the file).
    pub captures: Vec<String>,
}

/// A stated parameter type (M3-G3): a kind, or a limit.
#[derive(Clone, Debug, PartialEq)]
pub enum ParamType {
    K(Kind),
    /// `as number`: any number kind, checked per instance as anything that
    /// can add and compare (M3-S10).
    Number,
    /// plain `anything` (M3-G4): the input is generic (M3-S8).
    Any,
    /// anything that can VERB and VERB (M3-G4)
    Limited(Vec<String>),
}

/// An interface (ch.23): Anything that can VERB must have FN.
#[derive(Clone, Debug)]
pub struct Interface {
    pub verb: String,    // speak
    pub fn_name: String, // speak (the promised function)
    /// By default FN says nothing. / By default FN says TEXT.
    /// None = no default; Some("") = says nothing (gives the empty text);
    /// Some(t) = gives the text t.
    pub default: Option<String>,
}

/// The special meanings (ch.26, M3-D4): can add, can compare, can copy,
/// can clean up, can be saved.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Meaning {
    Add,
    Compare,
    Copy,
    CleanUp,
    Saved,
}

/// An implementation block (ch.23): A dog can speak. (functions) or
/// A point can add. (a special meaning, statements).
#[derive(Clone, Debug)]
pub struct ImplBlock {
    pub kind_name: String, // dog / point
    pub verb: String,      // speak / add
    pub meaning: Option<Meaning>,
    pub funcs: Vec<FuncDef>, // for function impls
    pub body: Vec<Stmt>,     // for meaning impls
    pub line: usize,
}

/// How a function receives an input (ch.28):
/// Lent: read only, the caller keeps the value (the default).
/// LentToChange: unique borrow, the function may change it.
/// MoveIn: the value is moved into the function, the old name is dead.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ParamMode {
    Lent,
    LentToChange,
    MoveIn,
}

#[derive(Clone, Debug)]
pub enum FnBody {
    Expr(Expr),
    Block(Vec<Stmt>),
}

pub struct Program {
    pub body: Vec<Stmt>,
    pub funcs: Vec<FuncDef>,
    pub tests: Vec<TestDef>, // Test blocks (ch.38), run by `lykaon test`
    // ---- M3 ----
    pub interfaces: Vec<Interface>, // Anything that can VERB must have FN.
    /// The implementation blocks, in file order.
    pub impls: Vec<ImplBlock>,
    /// The always block of a record: A person has ... / Always age is at least 0.
    /// (ch.64, M3-S38): type name -> conditions.
    pub always: Vec<(String, Contract)>,
    /// Lykaon.toml facts if the program root is a package folder (ch.37):
    /// name, version, edition, entry, needs, allows.
    pub package: Option<PackageDecl>,
    /// M4-S29: the folder relative file paths resolve against (the folder
    /// of the program's file - the package folder for a package root).
    pub source_dir: String,
    /// M4-8 (Appendix K 7.11): the tool's positional arguments (Takes NAME
    /// as T., M4-G25) and flags (Option NAME is T., M4-G26), in program
    /// order. Both must stand before every other sentence except Note and
    /// About (T0174, M4-S81).
    pub takes: Vec<ToolArg>,
    pub options: Vec<ToolOpt>,
}

/// A dependency and the permissions of a package (ch.37).
#[derive(Clone, Debug)]
pub struct PackageDecl {
    pub name: String,
    pub version: Option<(u64, u64, u64)>,
    pub edition: Option<u64>,
    pub entry: Option<String>,
    pub needs: Vec<Need>,
    pub allows: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct Need {
    pub name: String,
    pub version_req: Option<(Option<u64>, Option<(Option<u64>, Option<u64>)>)>, // major (minor (patch))
    /// Needs X from folder a in folder b (M3-S3: the only accepted form).
    pub folder: Vec<String>,
}

/// A collected test block: name and the statements inside it (ch.38).
pub struct TestDef {
    pub name: String,
    pub body: Vec<Stmt>,
}
