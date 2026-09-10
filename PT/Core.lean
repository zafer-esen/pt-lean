import Lean

namespace PT

open Lean in
/-- Only `proof` may apply the `pt_proof` attribute. -/
initialize taggingProof : IO.Ref Bool ← IO.mkRef false
open Lean in

initialize proofTag : TagAttribute ←
  registerTagAttribute `pt_proof "written as a proof block" fun _ => do
    unless ← taggingProof.get do throwError "`pt_proof` marks a `proof` block, it is not written by hand"
open Lean in

initialize anonTag : TagAttribute ← registerTagAttribute `pt_anon "a proof block without a name"
open Lean in

initialize relaxedTag : TagAttribute ← registerTagAttribute `pt_relaxed "checked with weakened options"

def T : Prop := True
def F : Prop := False
def Imp (p q : Prop) : Prop := p → q
notation:25 a:26 " ⇒ " b:26 => Imp a b

def even (x : Int) : Prop := x % 2 = 0
def odd (x : Int) : Prop := x % 2 = 1
@[simp] theorem even_def (x : Int) : even x = (x % 2 = 0) := rfl
@[simp] theorem odd_def (x : Int) : odd x = (x % 2 = 1) := rfl

theorem T.intro : T := trivial

theorem iffT {p : Prop} (hp : p) : p ↔ T := ⟨fun _ => trivial, fun _ => hp⟩
theorem F.elim' {p : Prop} (h : F) : p := False.elim h
@[simp] theorem T_def : T = True := rfl
@[simp] theorem F_def : F = False := rfl
@[simp] theorem Imp_def (p q : Prop) : (p ⇒ q) = (p → q) := rfl

open Lean PrettyPrinter in

@[app_unexpander Iff] def unexpandIff : Unexpander
  | `($_ $p $q) => `($p = $q)
  | _ => throw ()

@[refl] theorem Imp.refl (p : Prop) : p ⇒ p := fun h => h
theorem Imp.of_eq {a b : Prop} (h : a = b) : a ⇒ b := h ▸ Imp.refl a
theorem Imp.trans {p q r : Prop} (h₁ : p ⇒ q) (h₂ : q ⇒ r) : p ⇒ r := fun hp => h₂ (h₁ hp)

theorem Imp.and_mono {a b c d : Prop} (h₁ : a ⇒ b) (h₂ : c ⇒ d) : a ∧ c ⇒ b ∧ d :=
  fun ⟨ha, hc⟩ => ⟨h₁ ha, h₂ hc⟩
theorem Imp.or_mono {a b c d : Prop} (h₁ : a ⇒ b) (h₂ : c ⇒ d) : a ∨ c ⇒ b ∨ d :=
  fun h => h.elim (fun ha => Or.inl (h₁ ha)) (fun hc => Or.inr (h₂ hc))
/-- Monotonicity followed by comparison up to associativity and commutativity. -/
theorem Imp.and_left_ac {a a' b c : Prop} (h : a ⇒ a') (h' : (a' ∧ b) ↔ c) : a ∧ b ⇒ c :=
  fun ⟨x, y⟩ => h'.mp ⟨h x, y⟩
theorem Imp.and_right_ac {a b b' c : Prop} (h : b ⇒ b') (h' : (a ∧ b') ↔ c) : a ∧ b ⇒ c :=
  fun ⟨x, y⟩ => h'.mp ⟨x, h y⟩
theorem Imp.or_left_ac {a a' b c : Prop} (h : a ⇒ a') (h' : (a' ∨ b) ↔ c) : a ∨ b ⇒ c :=
  fun z => h'.mp (z.elim (fun x => Or.inl (h x)) Or.inr)
theorem Imp.or_right_ac {a b b' c : Prop} (h : b ⇒ b') (h' : (a ∨ b') ↔ c) : a ∨ b ⇒ c :=
  fun z => h'.mp (z.elim Or.inl (fun y => Or.inr (h y)))
theorem Imp.not_anti {a b : Prop} (h : b ⇒ a) : ¬a ⇒ ¬b := fun hna hb => hna (h hb)
theorem Imp.imp_mono {a b c d : Prop} (h₁ : c ⇒ a) (h₂ : b ⇒ d) : (a ⇒ b) ⇒ (c ⇒ d) :=
  fun hab hc => h₂ (hab (h₁ hc))

instance : Std.Commutative And := ⟨fun _ _ => propext and_comm⟩
instance : Std.Commutative Or := ⟨fun _ _ => propext or_comm⟩

theorem Imp.congr {a a' b b' : Prop} (ha : a ↔ a') (hb : b ↔ b') : (a ⇒ b) ↔ (a' ⇒ b') :=
  ⟨fun h x => hb.mp (h (ha.mpr x)), fun h x => hb.mpr (h (ha.mp x))⟩

theorem Imp.congr_right {a b b' : Prop} (hb : a → (b ↔ b')) : (a ⇒ b) ↔ (a ⇒ b') :=
  ⟨fun h x => (hb x).mp (h x), fun h x => (hb x).mpr (h x)⟩

theorem of_ac {a b : Prop} (h : a) (hab : a = b) : b := hab ▸ h

theorem Imp.of_iff {a b : Prop} (h : a ↔ b) : a ⇒ b := fun x => h.mp x
theorem step_ee {a b c : Prop} (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c := h₁.trans h₂
theorem step_ei {a b c : Prop} (h₁ : a ↔ b) (h₂ : b ⇒ c) : a ⇒ c := fun ha => h₂ (h₁.mp ha)
theorem step_ie {a b c : Prop} (h₁ : a ⇒ b) (h₂ : b ↔ c) : a ⇒ c := fun ha => h₂.mp (h₁ ha)
theorem step_ii {a b c : Prop} (h₁ : a ⇒ b) (h₂ : b ⇒ c) : a ⇒ c := Imp.trans h₁ h₂

theorem of_equiv_T {a : Prop} (h : a ↔ T) : a := h.mpr T.intro

theorem of_imp_T {a : Prop} (h : T ⇒ a) : a := h T.intro

/-- Truth-table proof for the trusted axioms -/
syntax "truth_table" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| truth_table) => `(tactic| simp_all [T_def, F_def, Imp_def])
  | `(tactic| truth_table $x:ident $xs:ident*) =>
    `(tactic| (open Classical in by_cases $x:ident <;> truth_table $xs*))

end PT
