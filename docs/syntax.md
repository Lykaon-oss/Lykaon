# Lykaon syntax — the 5-minute tour

Lykaon code is plain English sentences. Every sentence ends with a period (`.`).
A block is the indented sentences under an opener. There are **no quoted strings**:
words in code are raw text, and the compiler refuses quote marks (`Error: Quote in code. (T0008)`).

## A minimal program

```lykaon
Say hello world from Lykaon today.
```

Run it with the interpreter:

```
lykaon-cli run hello.lykaon
```

or build a real executable with the compiler:

```
lykaonc-cli build fast hello.lykaon hello.exe
hello.exe
```

On Windows, `hello.exe` is a standalone native program. See [`cli.md`](cli.md)
for every option.

## Variables and data kinds

A name is introduced by `Changeable` (you may re-set it), `Constant` (may not change),
or a plain definition (also may not change):

```lykaon
Changeable score is 10.
Constant limit is 5.
Total is 20.
Set score to score plus Total.
Say score.
```

Kinds are written the way you say them:

| Kind words | Holds |
|---|---|
| `whole number` | an integer (the default for plain numbers) |
| `number` | a whole or a decimal |
| `decimal` | a decimal number (`3 is a decimal.`) |
| `text` | words |
| `yes or no` | true/false |
| `maybe number` | a value or `missing` |
| `list of number`, `map of text to number`, `set of text`, `pair of number and text` | collections |
| `date`, `moment`, `duration`, `secret` | M4 kinds |

`Ask` reads one line from the keyboard into a name; `missing` and `fallback` handle absence:

```lykaon
Ask name.
Say hello name.
Phone is missing as maybe number.
If phone is missing say no phone.
Say phone fallback 0.
```

## Control flow

One-line `If` or an indented block, `Otherwise`, chained `Otherwise if`;
`Repeat` for loops; `For each` over collections or ranges; `Stop` and `Skip`:

```lykaon
Age is 20.
If age is at least 18 and age is at most 65.
    Say working age.
Otherwise.
    Say not working age.

Repeat 3 times say hi.
Repeat 3 times.
    Say round.

Count is 1.
Repeat while count is at most 3.
    Say count.
    Set count to count plus 1.

Numbers is list of 5 and 2 and 8.
For each n in numbers.
    Say n times 2.
For each i from 1 to 5.
    Say i.
For each name and age in ages.
    Say name age.
```

Comparison phrases: `is`, `is not`, `is more than`, `is less than`,
`is at least`, `is at most`, joined with `and` / `or`.
The word `it` means *the last result*; `them` means the last list.

## Functions and modules

`To` defines a function, `Give back` returns a value, and a one-line body is allowed:

```lykaon
To double x give back x times 2.
Say double 21.
```

A block body:

```lykaon
To sumto n.
    Total is 0.
    For each i from 1 to n.
        Set Total to Total plus i.
    Give back Total.
Say sumto 100.
```

Functions can fail, and `Try` catches the failure (`it` holds the value,
`If that fails.` catches):

```lykaon
To halve n can fail.
    If n is 0 fail with zero cannot be halved.
    Give back n divided by 2.
Try halve 0.
    Say it.
If that fails.
    Say could not halve.
```

Split a program across files with `Use`, and expose names with `Share`:

```lykaon
Use settings.
Say greeting.
Say double 21.
```

A package needs a `Lykaon.toml` next to it:

```lykaon
Name is myapp.
Version is 1 point 0 point 0.
Needs helpers from folder helpers.
Needs tools from git https://example.com/tools.git at version 1 point 2 point 0.
```

Manage it with `lykaon add`, `lykaon remove`, `lykaon update` (see [`cli.md`](cli.md)).

## Records, enums and interfaces

```lykaon
A person has name as text and age as number.
Maya is a person with name Maya and age 31.
Say name of maya.

A color is red or green or blue.
Shade is green.
Look at shade.
    When red.
        Say warm.
    When green.
        Say fresh.

Anything that can speak must have speak.
A dog has name as text.
A dog can speak.
    To speak pet give woof.
Rex is a dog with name Rex.
Say speak Rex.
```

## A working example: a tiny HTTP server

```lykaon
Counter is 0.

Serve on port 8080.
    When someone gets home.
        Set Counter to Counter plus 1.
        Respond with hello visitor number Counter.
    When someone gets users page.
        Name is parameter user of the request.
        Respond with json Name.
```

`Serve` listens until the program ends. Each request runs as its own task;
`parameter user of the request` reads `/users?user=Maya`; `Respond with json`
returns status 200 with `application/json`. Put the program in a file and run:

```
lykaon-cli run server.lykaon
```

then open `http://localhost:8080` in a browser.

## Next steps

- [`standard-library.md`](standard-library.md) — every built-in word, grouped by task
- [`cli.md`](cli.md) — run, repl, build, test, packages, benchmarks
- [`Lykaon_Language_Reference.docx`](Lykaon_Language_Reference.docx) — the complete reference for v0.1
