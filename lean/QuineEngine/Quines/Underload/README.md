# Underload

An ordinary quine in Underload, obtained from the engine.

| File | Contents |
| --- | --- |
| `Underload.lean` | the language, the instance of the engine, and the proof |
| `underload.ul` | the quine, written by `lake exe quine` |

## The language

Underload is a small Turing-complete esoteric language. A program is a string of one-character
commands acting on a stack of strings:

| Command | Effect |
| --- | --- |
| `(…)` | push a literal |
| `:` | duplicate |
| `!` | drop |
| `~` | swap |
| `*` | concatenate |
| `a` | wrap in parentheses |
| `S` | print |
| `^` | evaluate |

Texts are `List Char`.

## The development

- **Machine.** `exec` is an interpreter with fuel. `Runs t out` says that some amount of fuel makes
  `t` terminate printing `out`. `walk` tracks parenthesis depth, `Balanced` is the resulting
  well-formedness predicate, and `parseLit` reads a literal.
- **System.** A program displays as what it prints, and rendering and scanning are identities. So
  a generalized quine here is an ordinary quine.
- **Instance.** The quotation is `q t = (t)S` on balanced strings. The substitution is
  `sub a x = (x)a`, and the template is `:aSS`.
- **Lemmas.**
  - `runs_print`: `(t)S` prints `t`.
  - `runs_dup`: `(x):aSS` prints `(x)x`.
  - `balanced_dup`: `(x)x` is balanced whenever `x` is.
  - `exec_det`: every program prints at most one string.
  - Supporting facts about the depth walk and literal parsing: `walk_append`, `walk_shift` and
    `parseLit_balanced`.
- **Result.** The engine's fixed point `quine` is `(:aSS):aSS`. `quine_correct` proves that it is
  a quine, with its side conditions closed by `decide`. It depends only on the axioms `propext`
  and `Quot.sound`.
