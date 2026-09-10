import PT.Core

namespace PT

def Forall {α : Type} (R P : α → Prop) : Prop := ∀ x, R x → P x

def Ex {α : Type} (R P : α → Prop) : Prop := ∃ x, R x ∧ P x

def Summation (m n : Int) (e : Int → Int) : Int := go (n - m).toNat
where go : Nat → Int
  | 0 => 0
  | k + 1 => go k + e (m + k)

def Product (m n : Int) (e : Int → Int) : Int := go (n - m).toNat
where go : Nat → Int
  | 0 => 1
  | k + 1 => go k * e (m + k)

noncomputable def Count (m n : Int) (p : Int → Prop) : Int :=
  Summation m n fun i => open Classical in if p i then 1 else 0

theorem Forall.congr {α : Type} {R R' P P' : α → Prop}
    (hR : ∀ x, R x ↔ R' x) (hP : ∀ x, R x → (P x ↔ P' x)) : Forall R P ↔ Forall R' P' := by
  constructor
  · intro h x hx'
    have hx := (hR x).mpr hx'
    exact (hP x hx).mp (h x hx)
  · intro h x hx
    exact (hP x hx).mpr (h x ((hR x).mp hx))
theorem Ex.congr {α : Type} {R R' P P' : α → Prop}
    (hR : ∀ x, R x ↔ R' x) (hP : ∀ x, R x → (P x ↔ P' x)) : Ex R P ↔ Ex R' P' := by
  constructor
  · intro ⟨x, hx, px⟩
    exact ⟨x, (hR x).mp hx, (hP x hx).mp px⟩
  · intro ⟨x, hx', px'⟩
    have hx := (hR x).mpr hx'
    exact ⟨x, hx, (hP x hx).mpr px'⟩

/-! Term notation for `N` would reserve the name. -/

syntax:50 term:51 " ≤ " term:51 " < " term:51 : term
macro_rules | `($a ≤ $b < $c) => `($a ≤ $b ∧ $b < $c)

syntax:lead "∀ " ident " : " term " : " term : term
syntax:lead "∃ " ident " : " term " : " term : term
syntax:lead "Σ " ident " : " term:51 " ≤ " ident " < " term:51 " : " term : term
syntax:lead "Π " ident " : " term:51 " ≤ " ident " < " term:51 " : " term : term
macro_rules
  | `(∀ $i:ident : $r : $b) => `(PT.Forall (fun $i => $r) (fun $i => $b))
  | `(∃ $i:ident : $r : $b) => `(PT.Ex (fun $i => $r) (fun $i => $b))
  | `(Σ $i:ident : $m ≤ $j:ident < $n : $e) => do
    unless i.getId == j.getId do Lean.Macro.throwErrorAt j s!"the dummy is `{i.getId}`, not `{j.getId}`"
    `(PT.Summation $m $n (fun ($i : Int) => $e))
  | `(Π $i:ident : $m ≤ $j:ident < $n : $e) => do
    unless i.getId == j.getId do Lean.Macro.throwErrorAt j s!"the dummy is `{i.getId}`, not `{j.getId}`"
    `(PT.Product $m $n (fun ($i : Int) => $e))

open Lean PrettyPrinter in
@[app_unexpander PT.Forall] def unexpandForall : Unexpander
  | `($_ $R $P) => match R, P with
    | `(fun $i:ident => $r), `(fun $j:ident => $b) =>
      if i.getId == j.getId then `(∀ $i : $r : $b) else throw ()
    | `(fun $i:ident => $r), p => `(∀ $i : $r : $p $i)
    | _, _ => throw ()
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander PT.Ex] def unexpandEx : Unexpander
  | `($_ $R $P) => match R, P with
    | `(fun $i:ident => $r), `(fun $j:ident => $b) =>
      if i.getId == j.getId then `(∃ $i : $r : $b) else throw ()
    | `(fun $i:ident => $r), p => `(∃ $i : $r : $p $i)
    | _, _ => throw ()
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander PT.Summation] def unexpandSummation : Unexpander
  | `($_ $m $n $E) => match E with
    | `(fun $i:ident => $e) => `(Σ $i : $m ≤ $i < $n : $e)
    | _ => throw ()
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander PT.Product] def unexpandProduct : Unexpander
  | `($_ $m $n $E) => match E with
    | `(fun $i:ident => $e) => `(Π $i : $m ≤ $i < $n : $e)
    | _ => throw ()
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander And] def unexpandRange : Unexpander
  | `($_ $x $y) => match x, y with
    | `($a ≤ $i:ident), `($j:ident < $b) =>
      if i.getId == j.getId then `($a ≤ $i < $b) else throw ()
    | _, _ => throw ()
  | _ => throw ()

end PT
