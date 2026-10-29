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
- Use `assume A, B, ...` to prove `A ∧ B ∧ ... ⇒ C` by showing `C`. Refer to assumptions with `{Assumption: A}`. Add `Conditional Substitution` when a rule's condition comes from an assumption. A condition that is only part of the formula is used with Substitution (2.33) or Replace by T (2.34).
- Arithmetic is also supported, e.g., `{Arithmetic: m ≤ m + 1}`. The arithmetic formula must always be specified. A fact that follows from assumptions is cited with them, e.g., `{Assumption: y > 0, Assumption: r ≥ y, Arithmetic: 0 < r}`.

An implication proved with `assume`:

```lean
import PT

proof example2 (p q) : p ∧ q ⇒ p ∨ q
assume p, q
    p ∨ q
= {Assumption: p}
    T ∨ q
= {Or-simplification}
    T
qed
```

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

A chain such as `0 ≤ r < y` is read as `0 ≤ r ∧ r < y`. `x ≥ y` is the same formula as `y ≤ x`, `x > y` as `y < x` and `x ≠ y` as `¬(x = y)`.

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
  do x > 0 →
       x := x - 1
  od
  {R : x = 0}

obligations countdown
```

The names of the proof goals and their form can be listed with `obligations countdown`. In a proof of its own under that name, each goal is stated for this program and proved, e.g., `proof countdown.init : …`. Sums and differences in the integer terms of a statement may be simplified, e.g., `x + 1 - y - 1` to `x - y`. A wrong statement is rejected with the part that differs. Whether all goals are stated and proved can be checked with `verified countdown`.

In a proof whose name starts with `countdown.`, the annotation names Q, P and R may be used for their formulas, e.g., `proof countdown.post : P ∧ ¬(x > 0) ⇒ R`. The code, the guards and the bound are written out. A step in which a name is only replaced by its formula is justified by its definition, e.g., `{Definition of P}`.

A `program` can also be a single alternative command `if … fi` between `{Q : …}` and `{R : …}`. Its goals are those of the Alternative Command Theorem, named `guards`, `branch1`, `branch2`, and so on.

The generated decrease obligations use `t1 : Int` to save the bound. (Do not use `t1` in program code or in annotations.)

## Procedures

A recursive procedure is written with `proc`, its precondition, its bound, its body and its postcondition. The recursive call is written with its triple `{Q'} P() {R'}` and the theorems by which this triple is obtained from `{Q} P() {R}`, in braces right after `{R' : …}`. These are Substitution Theorem I or II with the substitution, e.g., `{Substitution Theorem I: Y := Y - 1}`, and the Invariance Theorem with a formula, followed by the Conjunction Theorem. Q' and R' may be written in any form equal by arithmetic to what is obtained by the theorems. A call written as `P()` alone has the triple `{Q} P() {R}`.

```lean
import PT
open PT

state n t1 t2 Y : Int

proc Keep
  {Q : n = Y ∧ n ≥ 0}
  {bound t : n + 1}
  if n = 0 →
       skip
  □ n > 0 →
       n := n - 1;
       {Q' : n = Y - 1 ∧ n ≥ 0}
       Keep()
       {R' : n = Y - 1 ∧ n ≥ 0}
       {Substitution Theorem I: Y := Y - 1};
       n := n + 1
  fi
  {R : n = Y ∧ n ≥ 0}

obligations Keep
```

The goals can be listed with `obligations Keep`. They are those of the Alternative Command Theorem for the outer `if`, `before` and `after` of the Recursion Theorem for the code around the call, and `bound` and `dec` for termination. A call may be a command of the body or of a branch of the outer `if`, one per branch, and only the procedure itself may be called. In the decrease obligation, `t1 t2 : Int` are used for the bound at the start of the procedure and at the call, so they may not occur in the procedure or its annotations. In the proofs of `Keep`, Q' and R' may also be used for the formulas of the triple of the call.

## Other

`status` lists proved, unfinished, and flagged proofs.

`set_option pt.check false` disables the automated checker.

## License and sources

Licensed under [MIT](LICENSE).

Rule names and numbering follow Parosh Aziz Abdulla's Programming Theory compendium.
