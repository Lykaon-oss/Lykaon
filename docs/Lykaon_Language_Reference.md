# Lykaon Language Reference — Version 0.1 (M1–M4)

*Complete Build Reference for Lykaon v0.1. Normalized for the Lykaon name
throughout (the language's own name; no legacy names). Everything here matches
the conformance test suite in the repository.*

---

## 1. About this reference

Lykaon is a programming language written in plain English sentences.

- A **sentence** ends with a period (`.`).
- A **block** is the indented sentences under an opener sentence.
- There are **no quoted strings**: words in code are raw text. Quote marks are
  refused with `Error: Quote in code. (T0008)`.
- Comments and documentation are `Note` and `About` sentences.
- Names are letters and digits (e.g. `score`, `Number2`).

Version 0.1 covers milestones M1–M4: language core, data and ownership, native
compilation, and servers/concurrency. Windowed (GUI) apps arrive in a later
version; v0.1 programs are command-line and console executables.

---

## 2. Names and values

| Sentence | Meaning |
|---|---|
| `Changeable x is 10.` | introduce a name you may re-set |
| `Constant limit is 5.` | introduce a name that may not change |
| `Total is 20.` | plain immutable definition |
| `Set x to 3.` | give a changeable name a new value |
| `Ask name.` | read one line from the keyboard into `name` |
| `Say hello.` | print (one sentence may print several values) |

Block printing:

```lykaon
Say lines.
    first line
    second line
```

- `it` means *the last result*; `them` means *the last list*.
- `Ask` fails with *no person here* when stdin is not a terminal
  (use `For each line in input.` for piped input).

### Kinds

| Kind words | Holds |
|---|---|
| `whole number` | integer (plain numbers are whole numbers) |
| `number` | whole or decimal |
| `decimal` | decimal number |
| `text` | words |
| `yes or no` | true/false |
| `maybe T` | a value of kind T or `missing` |
| `list of T`, `map of K to V`, `set of T`, `pair of A and B` | collections |
| `channel of T holding N` | bounded channel |
| `guarded of T`, `atomic`, `counter` | shared values |
| `date`, `moment`, `duration`, `secret` | time/secret values |

Kinds may be given at definition: `Phone is missing as maybe number.`

---

## 3. Numbers, text and comparisons

Operations: `plus`, `minus`, `times`, `divided by`, `whole divided by`,
`rem`, `pow`. Rounding: `rounded`, `rounded to even`. Conversion: `as decimal`.

Comparisons (used with `If`, `Repeat while`, `where`, contracts):

```
is, is not, is more than, is less than, is at least, is at most
```

Compound conditions join with `and` and `or`.

Text is grapheme-aware; `position of x in y`, `how many in x`, `starts with`,
`ends with`, `contains`. Text ordering is by Unicode code point.

---

## 4. Collections

```lykaon
Numbers is list of 5 and 2 and 8.
Names is empty list of text.
Say item 2 of numbers.
Say first 2 of numbers.
Say last of numbers.
Say items 2 to 3 of numbers.
Say how many in numbers.
Say if numbers is empty.
Spot is position of 8 in numbers.
Say spot fallback 0.
Add 9 to nums.
Remove 2 from nums.
Say numbers sorted.
Say numbers sorted descending.
Say numbers reversed.
Say 3 and 3 and 4 unique.
Say numbers where it is more than 3.
```

Maps, sets and pairs:

```lykaon
Ages is map of text to number.
Put 31 in ages under Maya.
Found is value of Maya in ages.
Say found fallback 0.
Say if ages has Maya.
For each name and age in ages.
    Say name age.
Remove Maya from ages.

Tags is set of text.
Put red in tags.
Say union of left and right.
Say overlap of left and right.
Say difference of left and right.

Pair is pair of 1 and 2.
Say first of pair.
Say second of pair.
```

---

## 5. Records, enums and `Look at`

```lykaon
A person has name as text and age as number.
Maya is a person with name Maya and age 31.
Say name of maya.
Say age of maya.

A color is red or green or blue.
Shade is green.
Look at shade.
    When red.
        Say warm.
    When green.
        Say fresh.
    When blue.
        Say cool.
```

`When <part name>` also looks *into* a record variant: `When card owner.`

Records can define `can compare` so `Less`/`More`/`AtLeast`/`AtMost` work on them.

---

## 6. maybe, missing, failure

```lykaon
Phone is missing as maybe number.
If phone is missing say no phone.
If phone is there say has phone.
Say phone fallback 0.
```

Functions may fail:

```lykaon
To halve n can fail.
    If n is 0 fail with zero cannot be halved.
    Give back n divided by 2.
Try halve 8.
    Say it.
If that fails.
    Say could not halve.
```

Checked and saturating math variants exist so overflow is an event, not a wrap.

---

## 7. Control flow

```lykaon
If age is at least 18.
    Say adult.
Otherwise if age is at least 13.
    Say teen.
Otherwise.
    Say child.

Repeat 3 times say hi.
Repeat 3 times.
    Say round.
Repeat forever.
    ...
Repeat while count is at most 3.
    ...
For each n in numbers.
    Say n.
For each i from 1 to 5.
    Say i.
For each name and age in ages.
    ...
For each line in file list.txt in temporary folder.
    Say line.
For each x as they arrive from channel.
    Say x.

Stop.
Skip.
```

`Stop` leaves the loop/round/scope; `Skip` starts the next round.

---

## 8. Functions

```lykaon
To double x give back x times 2.
Result is double 5.
Say Result.

To sumto n.
    Total is 0.
    For each i from 1 to n.
        Set Total to Total plus i.
    Give back Total.

To pad lend to change items.
    Add 0 to items.
    Give back how many in items.
```

- One-line bodies: `To head items give item 1 of items.`
- Interfaces pass the receiver as an input (`To speak pet give woof.`)
- `give` moves, `lend` borrows, `copy of x` copies, `share` shares, `weak` weakens
- A kind may define `can clean up.` with `Which is ...` — it runs when a value goes away

### Closures, Apply, Combine

Local `To` functions capture their surroundings at definition.
`Apply` calls a function once per list item; `Combine` folds a list with
`plus`, `minus` or `times`.

### Generators

```lykaon
To squares n
    For each i from 1 to n.
        Hand back i times i.

Say first 3 of squares 5.
```

`Hand back` suspends the function and yields one value per pull; body locals
persist between pulls. Built-ins like `first N of` are truly lazy.

---

## 9. Interfaces and dispatch

```lykaon
Anything that can speak must have speak.

A dog has name as text.
A dog can speak.
    To speak pet give woof.

A cat has name as text.
A cat can speak.
    To speak pet give meow.

Rex is a dog with name Rex.
Tom is a cat with name Tom.
Speakers is list of Rex and Tom.
For each s in Speakers.
    Say speak s.
```

- `Anything that can VERB must have VERB.` declares an interface
- `A KIND can VERB.` implements it; calls dispatch on the value's kind
- Static dispatch is devirtualized when the receiver's kind is known

---

## 10. Contracts

```lykaon
To halve n.
    Requires n is more than 0.
    Ensures result is more than 0.
    Give back n divided by 2.
Say halve 8.
```

- `Requires` is checked at every call (never skipped)
- `Ensures` is checked on return; the contract prover removes checks it proves
- `Always` on a kind is checked at construction and after `SetPart`
  (violation: `Error: Always failed: <cond>. (T0602)`, exit 1)
- `Tagged` marks kinds intentionally crossing safety boundaries
- Failed `Requires`: `Requires failed:`; `Ensures` likewise
- Unprovable results fail `T0603` instead of producing a value

---

## 11. Tests

```lykaon
Test halving works.
    Check halve 8 is 4.
    Check 2 plus 2 is 4.
    Pretend now is 2000-01-01 at 0 and 0.
```

- `Test NAME.` opens a test; `Check <a> is <b>.` asserts
- `Check for any` runs a property over generated values
- `Pretend` fixes time/random inside a test
- `lykaon-cli test file.lykaon` runs them; each test runs on a fresh frame

---

## 12. Modules and packages

```lykaon
Use settings.
Say greeting.
Share tripled.
```

- `Use NAME.` loads the file `NAME.lykaon` (or a package dependency)
- `Share NAME.` exposes a top-level name to users of the module
- Module load order is defined (start-up order, `M2-6`)
- `settings.lykaon` next to the program is read into top-level names automatically

`Lykaon.toml` (sentence format):

```lykaon
Name is myapp.
Version is 1 point 0 point 0.
Needs helpers from folder helpers.
Needs tools from git https://example.com/tools.git at version 1 point 2 point 0.
```

Commands: `lykaon add/remove/update` — see `cli.md`. Git deps are pinned by
tag and verified by a SHA-256 tree checksum in `lykaon.lock` (a rewritten tag
is refused with `Git dependency failed (T0520)`).

---

## 13. Tasks and concurrency

```lykaon
Start task looker.
    ... body ...
Wait for looker.

Do these together.
    Start task maker.
    Start task checker.

Stop task looker.
```

- `Start task NAME.` starts the block as a task and goes on
- `Wait for NAME.` gives the result to `it` (move kinds are taken once;
  a second wait on a taken result is `T0334`)
- `Do these together.` runs its task starts concurrently; its scope ends when
  every task ends (or a task fails, which cancels the rest)
- `Stop task NAME.` cancels; a finished task is a harmless no-op
- Task capture is checked: changing a captured `Changeable` from a task is
  refused (`T0451`); a value crossing tasks unsafely is `T0450`; a task kept
  past its block is `T0462`

Channels, guarded, atomic, counter:

```lykaon
Channel is a channel of text holding 100.
Send hello to channel.
Receive from channel.
Box is a guarded of number.
Set box to 5.
Atomic count.          Add 2 to count atomically.
Counter clicks.        Set clicks to clicks plus 1.
```

- Channel capacity 1 to 1,000,000; `Send` pauses when full, `Receive` pauses
  when empty; `Receive` gives `missing` only when closed and empty
- Values are moved (move kinds) or copied (copy kinds) across the queue
- `guarded` is a one-key cell; `atomic` whole-number adds with `atomically`;
  `counter` counts with plain `plus`/`minus`

Workers and Spread:

```lykaon
Use 4 workers.
Spread the items over 4 workers.
    Say it.
```

`Use N workers.` (1–256) sizes the pool; `Spread` runs one round per item
with the item in `it`; results collect in item order; a failing round stops
the rest.

---

## 14. Timers

```lykaon
After 5 seconds.
    Say time is up.
Every 10 minutes.
    Say still here.
Sleep for 2 seconds.
```

- Plural units only: `seconds`, `minutes`, `hours`, `days`
- `After` fires once, at its deadline; `Every` repeats at a fixed rate
  (rounds never overlap); `Stop.` inside a round ends the round
- The program stays alive while an `After` is pending in its main scope
- `Every` without a `Sleep for` fires nothing in v0.1 (logged limitation)

---

## 15. Files, folders, zip

```lykaon
Write 42 to file score.txt in temporary folder.
Say Read file score.txt in temporary folder.
Read bytes of file data.bin in temporary folder.
Append 7 to file log.txt in temporary folder.
Replace file data.txt in temporary folder with 2.
For each line in file list.txt in temporary folder.
    Say line.
Make folder backup in temporary folder.
Remove file old.txt in temporary folder.
Remove folder backup in temporary folder.
Move file a.txt in temporary folder to file b.txt in temporary folder.
Duplicate file a.txt in temporary folder to file c.txt in temporary folder.
Say if file b.txt in temporary folder exists.
Say the files in folder backup in temporary folder.
Make a temporary file as scratch.
When file watch.txt changes.
    Say it changed.
Zip folder backup in temporary folder to file pack.zip in temporary folder.
Unzip file pack.zip in temporary folder to folder out in temporary folder.
Gzip file big.txt in temporary folder to file big.gz in temporary folder.
```

- Roots: `in temporary folder` (OS temp dir), `in folder X` (chained steps);
  a bare name resolves next to the program file
- `Write` refuses to overwrite an existing non-temporary file;
  `Replace` is atomic (sibling temp file + one rename)
- `Read` keeps line endings; `For each line` streams lines without endings
- A missing file is an anonymous *not found* failure
- `List files in` returns names sorted; `Zip` writes deflate archives with
  sorted entries and a fixed stamp

---

## 16. Formats: JSON, TOML, YAML, XML, CSV

```lykaon
A creature has legs as number and eyes as number.
Save a creature with legs 3 and eyes 1 as json to file c.json in temporary folder.
Read json file c.json in temporary folder as creature.
Read json from text as whole number.
Say json of a creature with legs 2 and eyes 2.
```

- `Read <fmt> file F as KIND.` / `Read <fmt> from text V as KIND.` /
  `Save V as <fmt> to file F.`
- Format words: `json`, `toml`, `yaml`, `xml`, `csv`
- Decoding is kind-directed: record parts by name (extra keys ignored),
  lists from arrays, maps from objects (in order), enums as
  `{"kind": variant}`; depth limit 256
- `json of x` is compact; `Save ... as json` is pretty with a final line feed
- CSV needs a header row covering all record parts
- A decode mismatch is a diagnostic of the matching shape
  (`T0308` map key kind differs; `T0309` part kind differs)

---

## 17. Time, random, hash, secret

```lykaon
Use seed 42.
Say today.
Say now.
M is moment of today at 25 and 0.
Say m in zone Europe/Paris.
Say days between today and today plus 2 days.
Say random number from 1 to 10.
Say list of 1 and 2 and 3 shuffled.
Say hash of hello.
Key is secret hunter2.
Say reveal key.
```

- Kinds: `date`, `moment`, `duration`, `secret`
- `today`/`now` are local-zone; `in zone <IANA name>` converts (zones bundled;
  unknown zone is `T0171` at compile time)
- `moment of D at H and M` builds a moment; impossible dates are `T0620`
- Duration printing: `1 day and 2 hours`, singular at 1, `0 seconds` for zero
- `Use seed N.` makes random reproducible (Fisher–Yates for `shuffled`)
- `hash of` is SHA-256, 64 lower-case hex characters
- A `secret` never prints its text (a `Log` of one writes `hidden`), cannot be
  compared or converted; open it with `reveal`

---

## 18. System: Run, Exit, signals, environment, CLI tools

```lykaon
Say Run m48sayhi with first and second.
Exit with 0.
When signal interrupt arrives.
    Say stop requested.
Say Environment HOME as maybe text.
```

- `Run <program> with <args>.` runs a child process without a shell; its
  stdout is `it`; a nonzero child exit is a kind-other failure carrying the
  child's stderr
- `Exit with N` (0–255) ends the program after cleanups unwind
- Signals: `When signal interrupt/stop/hangup arrives.`; the poll happens
  after each sentence; a handlerless interrupt exits 130, stop 143, hangup 129
- `Environment NAME as maybe text` reads an environment variable (name is
  upper-cased with `_` for spaces)
- `Takes NAME as T.` and `Option NAME is T defaulting to V.` (before every
  other sentence except `Note`/`About`) make the file a command-line tool:

```lykaon
Takes file name as text.
Option verbose is whole number.
Option log level is text defaulting to debug.
```

  - positional arguments bind to `Takes` in order; `--name value` fills an
    `Option`; a bare `--flag` is the word `on` for text options
  - `--help` first prints usage and exits 0; a missing `Takes` argument or
    bad usage prints usage and exits 2
  - `Read input.` / `For each line in input.` stream stdin (empty stdin is
    zero rounds)

---

## 19. Logging

```lykaon
Use log level debug.
Log info server started.
Log warning hot.
Log error failed.
```

- Levels `debug`, `info`, `warning`, `error`; default `info`; logs go to
  standard error, program output to standard output, merged in order
- The log text is rendered exactly like `Say` (names, secrets hidden,
  counters shown)
- `Use log level X.` sets the floor; lower levels are not written

---

## 20. Network: Fetch, Serve, WebSocket

```lykaon
Reply is Fetch https://example.com/.
Say status of reply.
Say body of reply.
Posted is Post data to https://example.com/submit.

Serve on port 8080.
    When someone gets home.
        Respond with hello.
    When someone gets users page.
        Name is parameter user of the request.
        Respond with json Name.
    When someone posts new page.
        Respond with status 201.
    When someone opens live chat page.
        Send welcome to connection.
        Receive from connection.
```

- `Fetch` gives `{status, body, headers}`; status 400+ is a response, not a
  failure; requests retry until a deadline (sent-once rule)
- `Post x to <address>.` posts data; `Fetch ... without checking certificates.`
  only inside `Be careful.` (TLS skip variant)
- `Serve securely on port 8443 using certificate file C and key file K.` — TLS
- Pages: `When someone gets <page> page.` (also `posts`); inside, `method`,
  `page`, `text`, `data`, `header`, `query` and `parameter <name> of the
  request` are available
- Every path must reach exactly one `Respond with` (`T0166` otherwise)
- Answers: text (200), `json` (200, application/json), `status N`,
  `status N and <text>`, `template NAME` (fills `NAME.template`), and
  `literally <text>` for raw output
- Sessions: `Put x in the session under key.` / `value of key in the session`
  (30-minute expiry, HttpOnly SameSite=Lax cookie)
- WebSocket: `When someone opens <page> page.`; inside, `connection` is a
  first-class value; `Send x to connection.` sends a text frame;
  `Receive from connection.` gives maybe-text (missing on close)
- Port already in use: `T0618`; a page pattern must be unique (`T0172`);
  fetching an undeclared page is `T0173`

---

## 21. Diagnostics

Errors follow one shape:

```
Error: <message>. (T<code>)
Where: <file>, line N: <the sentence>
Why: <plain-English reason>
Fix: <suggested correction>
```

Common codes in v0.1:

| Code | Meaning |
|---|---|
| T0008 | a quote mark in code (Lykaon has no quoted text) |
| T0113 | the sentence does not fit any known shape |
| T0120 | two names of the same length both fit a word run (ambiguous) |
| T0130 | a two-reading (ambiguous) sentence |
| T0151 | `Try` around a sentence that cannot fail |
| T0158 | unknown dynamic kind (interface names no interface) |
| T0164 | `Limit` names no interface |
| T0166 | a Serve page path reaches no `Respond with` |
| T0168 | waiting/stopping an unknown task name |
| T0171 | unknown spelling (word/zone/program name) |
| T0172 | duplicate page pattern / missing template |
| T0173 | fetching an undeclared page |
| T0174 | `Takes`/`Option` after other sentences |
| T0205 | assignment to a name that is not changeable |
| T0207 | duplicate temporary file name |
| T0209 | a `Use` that is not a module Use |
| T0308 | map key kind differs (typed decode) |
| T0309 | record part kind differs (typed decode) |
| T0323 | kind cannot do that (e.g. dynamic kind mismatch) |
| T0324 | kind cannot compare (limit semantics) |
| T0334 | second wait on a taken move result |
| T0405–T0407 | shared-value misuse at `Set` |
| T0450 | a value crosses tasks unsafely |
| T0451 | a task changes a captured `Changeable` |
| T0460/T0462 | task cancellation / task outlives its block |
| T0515 | a folder dependency that is not next to the project |
| T0520 | git dependency failed (address, tag, checksum) |
| T0602 | `Always` failed |
| T0603 | a result left the whole-number domain (contract) |
| T0607 | call depth limit |
| T0618 | port in use |
| T0620 | impossible date |

---

## 22. Known limits in version 0.1

- Windows x86-64 is fully tested. Linux x86-64 cross-builds but the test
  suite has not been executed on Linux hardware yet.
- Roughly 67–72% of equivalent Rust speed on the six standard benchmarks.
- Windowed (GUI) apps are a later milestone; v0.1 builds command-line and
  console executables only.
- `Every` without a `Sleep for` fires nothing in v0.1.
- `can add` at run time is not implemented in v0.1.
- Some constructs (closures, Apply/Combine, dynamic dispatch, generators)
  evaluate through the embedded evaluator inside native builds; output is
  byte-identical to the interpreter by design and test.
