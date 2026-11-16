# The Lykaon standard library (v0.1)

Everything in this list is **built in** — there is nothing to import for it. File
modules loaded with `Use` add your own names on top. Words are grouped by task;
the book chapters that defined them are noted for reference.

## Numbers and math (Ch. 7)

- The four operations: `plus`, `minus`, `times`, `divided by`
- Whole-number forms: `whole divided by`, `rem`, `pow` (`2 pow 10`)
- Rounding: `rounded`, `rounded to even`; conversion: `as decimal`, `as whole number`

## Text (Ch. 8, 22)

- `position of x in y` (with `fallback`), `how many in x` for lengths
- `x sorted`, `x sorted descending`, `x reversed`, `x unique` (also on lists)
- English text patterns with `starts with`, `ends with`, `contains`
- Text ordering is by Unicode code point; text is grapheme-aware

## Collections (Ch. 12, M2)

Lists, maps, sets and pairs share one vocabulary:

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
Add 9 to nums.
Remove 2 from nums.
Ages is map of text to number.
Put 31 in ages under Maya.
Found is value of Maya in ages.
Say if ages has Maya.
Remove Maya from ages.
Say union of left and right.
Say overlap of left and right.
Say difference of left and right.
Pair is pair of 1 and 2.
Say first of pair.
Say second of pair.
Say numbers where it is more than 3.
```

- `Numbers where <condition>` filters a list
- Sets have `union`, `overlap` and `difference`

## Records, enums, `Look at` (Ch. 26, 31)

- `A person has name as text and age as number.` — record kind
- `Maya is a person with name Maya and age 31.` — value
- `A color is red or green or blue.` — enum kind
- `Look at x.` with `When <variant>.` arms — match on enums (and `When card owner.` into records)
- `name of record` reads a part; records that `can compare` work with `Less`/`More`/`AtLeast`/`AtMost`

## maybe, failure and fallback (Ch. 18, 19)

- `Phone is missing as maybe number.` / `If phone is there.` / `If phone is missing.`
- `x fallback <value>` — a default when `x` is `missing`
- `To halve n can fail.` / `fail with <message>` / `Try ... .` / `If that fails.`
- Checked and saturating math variants for overflow instead of wrapping

## Ownership (Ch. 20, M2)

- `give` (move), `lend` (borrow), `copy of x` (copy), `share` (shared handle), `weak`
- `clean up` — a kind may define `can clean up` with `Which is ...`; it runs when a value goes away

## Contracts (Ch. 64)

```lykaon
To halve n.
    Requires n is more than 0.
    Ensures result is more than 0.
    Give back n divided by 2.
```

- `Requires` — checked at every call
- `Ensures` — checked on return (the prover removes checks it can prove)
- `Always` — a kind invariant, checked on construction and `SetPart`
- `Tagged` — marks a kind for intentional unsafe cross-boundary use

## Tests (Ch. 61)

```lykaon
Test halving works.
    Check halve 8 is 4.
    Pretend now is 2000-01-01 at 0 and 0.
```

- `Test NAME.` with `Check <expr> is <expr>.` assertions
- `Pretend` fixes time/random for a test; `Check for any` runs a property
- Run them with `lykaon test` (see [`cli.md`](cli.md))

## Tasks and concurrency (Ch. 43, 44)

```lykaon
Start task looker.
    ... body ...
Wait for looker.
Do these together.
    Start task maker.
    Start task checker.
Stop task looker.
Use 4 workers.
Channel is a channel of text holding 100.
Send hello to channel.
Receive from channel.
Box is a guarded of number.
Atomic count. / Counter clicks.
Spread the items over 4 workers.
```

- `channel of <kind> holding N` — bounded queue (1 to 1,000,000)
- `guarded` — a value with one-key access; `atomic` — whole-number adds (`atomically`)
- `counter` — a whole-number counter; `plus`/`minus` on it is the atomic add
- `Use N workers.` sets the pool size (1–256); `Spread` gives each round to `it`

## Timers (Ch. 45)

```lykaon
After 5 seconds.
    Say time is up.
Every 10 minutes.
    Say still here.
Sleep for 2 seconds.
For each x as they arrive from channel.
    Say x.
```

- Durations: `seconds`, `minutes`, `hours`, `days` (plural forms)
- `After` fires once; `Every` repeats at a fixed rate; the program stays alive while a timer is pending
- `Sleep for` pauses; `For each ... as they arrive from NAME` drains a channel

## Files and folders (Ch. 47)

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
Move file a.txt in temporary folder to file b.txt in temporary folder.
Duplicate file a.txt in temporary folder to file c.txt in temporary folder.
Say if file b.txt in temporary folder exists.
Say the files in folder backup in temporary folder.
Make a temporary file as scratch.
Zip folder backup in temporary folder to file pack.zip in temporary folder.
Unzip file pack.zip in temporary folder to folder out in temporary folder.
Gzip file big.txt in temporary folder to file big.gz in temporary folder.
When file watch.txt changes.
    Say it changed.
```

- `in temporary folder` uses the OS temp dir; `in folder X` chains path steps;
  a bare file name resolves next to the program file
- `Write` refuses to overwrite an existing non-temporary file; `Replace` writes
  through a sibling temp file and one rename (atomic)

## Formats: JSON, TOML, YAML, XML, CSV (Ch. 48)

```lykaon
A creature has legs as number and eyes as number.
Save a creature with legs 3 and eyes 1 as json to file c.json in temporary folder.
Read json file c.json in temporary folder as creature.
Read json from text as whole number.
Say json of a creature with legs 2 and eyes 2.
```

- Format words: `json`, `toml`, `yaml`, `xml`, `csv` — in `Read <fmt> file F as KIND.`,
  `Read <fmt> from text <value> as KIND.` and `Save <value> as <fmt> to file F.`
- Decoding is kind-directed: record parts by name, lists to arrays, maps to objects
- `json of x` gives compact JSON text; `Save ... as json` writes pretty JSON
- CSV reads `list of <record kind>` with a header row

## Time, random, hash, secret (Ch. 49)

```lykaon
Use seed 42.
Say today.
Say now.
M is moment of today at 25 and 0.
Say m in zone Europe/Paris.
Say days between today and today plus 2 days.
Say random number from 1 to 10.
Say 3.5 as decimal rounded.
Say list of 1 and 2 and 3 shuffled.
Say hash of hello.
Key is secret hunter2.
Say reveal key.
```

- Kinds: `date`, `moment`, `duration`, `secret`
- `today`/`now` are local-zone; `in zone <IANA name>` converts; zones are bundled
- `Use seed N.` makes random reproducible; `hash of` is SHA-256 hex
- A `secret` never prints its text (a `Log` of one writes `hidden`) and must be
  opened with `reveal`

## System: Run, Exit, signals, environment, CLI (Ch. 46, 53)

```lykaon
Say Run m48sayhi with first and second.
Exit with 0.
When signal interrupt arrives.
    Say stop requested.
Say Environment HOME as maybe text.
Takes file name as text.
Option log level is text defaulting to debug.
For each line in input.
    Say line.
```

- `Run <program> with <args>` runs a child process (no shell); its stdout is `it`
- `Exit with N` ends the program with code N (0–255)
- `When signal interrupt/stop/hangup arrives.` registers a handler
- `Environment NAME as maybe text` reads an environment variable
- `Takes`/`Option` make the file a command-line tool: positional args and
  `--flag value` options, `defaulting to` values, automatic usage text
  (`--help` exits 0; bad usage exits 2), `Read input` streams stdin
- A `Takes NAME as T` argument that is absent prints the usage text and exits 2

## Logging and settings (Ch. 60)

```lykaon
Use log level debug.
Log info server started.
Log warning hot.
```

- Levels: `debug`, `info`, `warning`, `error` (default `info`); logs go to stderr
- `settings.lykaon` next to the program is read into top-level names automatically

## Network: Fetch, Serve, WebSocket (Ch. 51, 52)

```lykaon
Reply is Fetch https://example.com/.
Say status of reply.
Say body of reply.
Posted is Post data to https://example.com/submit.

Serve on port 8080.
    When someone gets home.
        Respond with hello.
    When someone gets users page.
        Respond with json users.
    When someone posts new page.
        Respond with status 201.
    When someone opens live chat page.
        Send welcome to connection.
        Receive from connection.
```

- `Fetch` gives a response record: `status`, `body`, `headers`; 400+ is a
  response, not a failure; `Post x to <address>` posts form data
- Pages: `When someone gets <page> page.` with `method`, `page`, `text`, `data`,
  `header`, `query`, `parameter <name> of the request` available in the block
- Answers: `Respond with <text>.`, `Respond with json x.`, `Respond with status N.`,
  `Respond with status N and <text>.`, `Respond with template NAME.`
- `Serve securely on port 8443 using certificate file C and key file K.` — TLS
- `When someone opens <page> page.` upgrades to WebSocket; inside, `connection`
  is a value: `Send x to connection.` and `Receive from connection.` (maybe text)
- Sessions: `Put x in the session under key.` / `value of key in the session` —
  30-minute expiry, secure cookies
