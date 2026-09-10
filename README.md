# lean-pt

A Lean checker for calculational proofs and program verification.

The tool works by translating each calculation to a Lean proof term. The [step checker](PT/Step.lean) tries the referenced rules in either direction and at different positions.

This is a pedagogical tool intended to provide live feedback to the user while carrying out such proofs.

## Usage

Install Lean and its VS Code extension using the [Lean setup guide](https://lean-lang.org/install/). Tested Lean version is at `lean-toolchain`.

Example:

```lean
import PT

proof example1 (p q) : p ∧ (p ⇒ q) = p ∧ q
    p ∧ (p ⇒ q)
= {Implication}
    p ∧ (¬p ∨ q)
= {Distributivity}
    (p ∧ ¬p) ∨ (p ∧ q)
= {Contradiction}
    F ∨ (p ∧ q)
= {Or-simplification}
    p ∧ q
qed

status
```

## Proof syntax

- Variables are typed, e.g., `(m n : Int)` or `(P : Int → Prop)`. Variables default to formulas (`Prop`).
- A calculation starts with a formula and ends with `qed`. An equality can be calculated from either side, or the whole statement reduced to `T` (or vice versa).
- Rules accept names. E.g., `{Implication}`. A formula can be specified explicitly in order to tell the tool where exactly a rule should apply, e.g.,`{Negation: p}`.
- Order and grouping of `∧` and `∨`, equality symmetry, and simple integer cancellation are automatic. Parentheses limit where rules apply. Use `{Commutativity}`, `{Associativity}`, or `{Identity}` when only rearranging a formula.
- Use `assume A, B, ...` to prove `A ∧ B ∧ ... ⇒ C` by showing `C`. Refer to assumptions with `{Assumption: A}`. Add `Conditional Substitution` when a rule's condition comes from an assumption or the surrounding formula.
- Arithmetic is also supported, e.g., `{Arithmetic: m ≤ m + 1}`. The arithmetic formula must always be specified.

## Notation

| Meaning | Notation | ASCII alternative |
| --- | --- | --- |
| Negation, conjunction, disjunction | `¬`, `∧`, `∨` | `~`, `/\`, `\/` |
| Implication | `⇒` | `=>`, `->` |
| Comparisons | `≤`, `≥`, `≠` | `<=`, `>=`, `!=` |
| Remainder | `mod` | `%` |
| Quantifiers | `∀`, `∃` | `forall`, `exists` |

Between formulas, `=` means equivalence. Between integers, it means equality. E.g., if `x` and `y` are integers, `x = y ∧ P` means `(x = y) ∧ P`.

Write predicates as `P(i)` or `P(i, j)` and ranged quantifiers as `∀ i : m ≤ i < n : P(i)`, with one dummy/bound variable per quantifier. `Σ` (sum), `Π` (product), and `N` (counting) use integer intervals.

Use `state x y : Int, b : Array` to declare program variables. Arrays have integer indices and values. `b[i : j] < x` has the range `[i,j]`. Division `/` is integer division. Powers need a numeral exponent.

## Programs

Programs use `skip`, `abort`, assignments, simultaneous assignments, sequencing with `;`, alternative command `if B → S □ C → U fi` and the iterative command. Use `□` or `|` between guards. Weakest preconditions can be written as `wp(x := x + 1, x > 0)`.

```lean
import PT
open PT

state x t1 : Int

program countdown
  {Q : x ≥ 0}
  {inv P : x ≥ 0}
  {bound t : x}
  do x > 0 → x := x - 1 od
  {R : x = 0}

obligations countdown
```

For the iterative command, `obligations` lists the proof goals. These need separate proofs named as listed, e.g.,`proof countdown.init : …`. `verified countdown` checks all goals.

The generated decrease obligations use `t1 : Int` to save the bound. (Do not use `t1` in program code or in annotations.)

## Other

`status` lists proved, unfinished, and flagged proofs.

`set_option pt.check false` disables the automated checker.

## License and sources

Licensed under [MIT](LICENSE).

Rule names and numbering follow Parosh Aziz Abdulla's Programming Theory compendium.
