import PT.Quantifiers

namespace PT

inductive Cmd (St : Type) where
  | skip
  | abort
  | seq (S₁ S₂ : Cmd St)
  | assign (f : St → St)
  | ifc (bs : List ((St → Prop) × Cmd St))

abbrev Pred (St : Type) := St → Prop

def bb {St : Type} : List ((St → Prop) × Cmd St) → St → Prop
  | [], _ => F
  | (B, _) :: bs, s => B s ∨ bb bs s

mutual
def wp {St : Type} : Cmd St → Pred St → St → Prop
  | .skip, R, s => R s
  | .abort, _, _ => F
  | .seq S₁ S₂, R, s => wp S₁ (wp S₂ R) s
  | .assign f, R, s => R (f s)
  | .ifc bs, R, s => bb bs s ∧ wpBranches bs R s

def wpBranches {St : Type} : List ((St → Prop) × Cmd St) → Pred St → St → Prop
  | [], _, _ => T
  | (B, S) :: bs, R, s => (B s ⇒ wp S R s) ∧ wpBranches bs R s
end

/-! ## Arrays (§5) -/

abbrev Arr := Int → Int

def upd (b : Arr) (i e : Int) : Arr := fun j => if j = i then e else b j

def SecEq (b : Arr) (i j x : Int) : Prop := ∀ k : i ≤ k < j + 1 : b k = x
def SecLt (b : Arr) (i j x : Int) : Prop := ∀ k : i ≤ k < j + 1 : b k < x
def SecGt (b : Arr) (i j x : Int) : Prop := ∀ k : i ≤ k < j + 1 : b k > x
def SecLe (b : Arr) (i j x : Int) : Prop := ∀ k : i ≤ k < j + 1 : b k ≤ x
def SecGe (b : Arr) (i j x : Int) : Prop := ∀ k : i ≤ k < j + 1 : b k ≥ x
def SecNe (b : Arr) (i j x : Int) : Prop := ∀ k : i ≤ k < j + 1 : b k ≠ x
def SecMem (x : Int) (b : Arr) (i j : Int) : Prop := ∃ k : i ≤ k < j + 1 : x = b k

-- 5.1
theorem AssignmentToArrayElement (b : Arr) (i j e f : Int) :
    upd b i e j = f ↔ (i = j ⇒ e = f) ∧ (i ≠ j ⇒ b j = f) := by
  unfold upd Imp
  by_cases h : j = i
  · subst h; simp
  · have h' : ¬ i = j := fun h'' => h h''.symm
    simp [h, h']
-- 5.2
theorem DefinitionOfArithmeticRelations.l1 (b : Arr) (i j x : Int) :
    SecEq b i j x ↔ (∀ k : i ≤ k < j + 1 : b k = x) := Iff.rfl
theorem DefinitionOfArithmeticRelations.l2 (b : Arr) (i j x : Int) :
    SecLt b i j x ↔ (∀ k : i ≤ k < j + 1 : b k < x) := Iff.rfl
theorem DefinitionOfArithmeticRelations.l3 (b : Arr) (i j x : Int) :
    SecGt b i j x ↔ (∀ k : i ≤ k < j + 1 : b k > x) := Iff.rfl
theorem DefinitionOfArithmeticRelations.l4 (b : Arr) (i j x : Int) :
    SecLe b i j x ↔ (∀ k : i ≤ k < j + 1 : b k ≤ x) := Iff.rfl
theorem DefinitionOfArithmeticRelations.l5 (b : Arr) (i j x : Int) :
    SecGe b i j x ↔ (∀ k : i ≤ k < j + 1 : b k ≥ x) := Iff.rfl
theorem DefinitionOfArithmeticRelations.l6 (b : Arr) (i j x : Int) :
    SecNe b i j x ↔ (∀ k : i ≤ k < j + 1 : b k ≠ x) := Iff.rfl
theorem DefinitionOfArithmeticRelations.l7 (b : Arr) (i j x : Int) :
    SecMem x b i j ↔ (∃ k : i ≤ k < j + 1 : x = b k) := Iff.rfl

/-! ## Properties of wp (§6) -/

variable {St : Type}

theorem wp_congr (S : Cmd St) (Q R : Pred St) (h : ∀ s, Q s ↔ R s) (s : St) :
    wp S Q s ↔ wp S R s := by
  have hQR : Q = R := funext fun s => propext (h s)
  subst hQR; exact Iff.rfl

mutual
private theorem wp_mono : ∀ (S : Cmd St) (Q R : Pred St), (∀ s, Q s → R s) →
    ∀ s, wp S Q s → wp S R s
  | .skip, _, _, h, s, hq => h s hq
  | .abort, _, _, _, _, hq => hq
  | .seq S₁ S₂, Q, R, h, s, hq =>
      wp_mono S₁ (wp S₂ Q) (wp S₂ R) (fun s' => wp_mono S₂ Q R h s') s hq
  | .assign f, _, _, h, s, hq => h (f s) hq
  | .ifc bs, Q, R, h, s, hq => ⟨hq.1, wpBranches_mono bs Q R h s hq.2⟩
private theorem wpBranches_mono : ∀ (bs : List ((St → Prop) × Cmd St)) (Q R : Pred St),
    (∀ s, Q s → R s) → ∀ s, wpBranches bs Q s → wpBranches bs R s
  | [], _, _, _, _, hq => hq
  | (_, S) :: bs, Q, R, h, s, hq =>
      ⟨fun hB => wp_mono S Q R h s (hq.1 hB), wpBranches_mono bs Q R h s hq.2⟩
end

mutual
private theorem wp_miracle : ∀ (S : Cmd St) (s : St), wp S (fun _ => F) s ↔ F
  | .skip, _ => Iff.rfl
  | .abort, _ => Iff.rfl
  | .seq S₁ S₂, s =>
      (wp_congr S₁ (wp S₂ (fun _ => F)) (fun _ => F) (fun s' => wp_miracle S₂ s') s).trans
        (wp_miracle S₁ s)
  | .assign _, _ => Iff.rfl
  | .ifc bs, s => wpBranches_miracle bs s
private theorem wpBranches_miracle : ∀ (bs : List ((St → Prop) × Cmd St)) (s : St),
    bb bs s ∧ wpBranches bs (fun _ => F) s ↔ F
  | [], _ => ⟨And.left, fun h => ⟨h, T.intro⟩⟩
  | (_, S) :: bs, s =>
      ⟨fun ⟨hor, hw⟩ => hor.elim (fun hB => (wp_miracle S s).mp (hw.1 hB))
          (fun hbb => (wpBranches_miracle bs s).mp ⟨hbb, hw.2⟩),
       fun h => False.elim h⟩
end

mutual
private theorem wp_and : ∀ (S : Cmd St) (Q R : Pred St) (s : St),
    wp S (fun s => Q s ∧ R s) s ↔ wp S Q s ∧ wp S R s
  | .skip, _, _, _ => Iff.rfl
  | .abort, _, _, _ => ⟨fun h => ⟨h, h⟩, And.left⟩
  | .seq S₁ S₂, Q, R, s =>
      (wp_congr S₁ (wp S₂ (fun s => Q s ∧ R s)) (fun s => wp S₂ Q s ∧ wp S₂ R s)
          (fun s' => wp_and S₂ Q R s') s).trans (wp_and S₁ (wp S₂ Q) (wp S₂ R) s)
  | .assign _, _, _, _ => Iff.rfl
  | .ifc bs, Q, R, s =>
      ⟨fun ⟨hb, hw⟩ =>
          ⟨⟨hb, ((wpBranches_and bs Q R s).mp hw).1⟩, ⟨hb, ((wpBranches_and bs Q R s).mp hw).2⟩⟩,
       fun ⟨⟨hb, h1⟩, ⟨_, h2⟩⟩ => ⟨hb, (wpBranches_and bs Q R s).mpr ⟨h1, h2⟩⟩⟩
private theorem wpBranches_and : ∀ (bs : List ((St → Prop) × Cmd St)) (Q R : Pred St) (s : St),
    wpBranches bs (fun s => Q s ∧ R s) s ↔ wpBranches bs Q s ∧ wpBranches bs R s
  | [], _, _, _ => ⟨fun h => ⟨h, h⟩, And.left⟩
  | (_, S) :: bs, Q, R, s =>
      ⟨fun ⟨h1, h2⟩ =>
          ⟨⟨fun hB => ((wp_and S Q R s).mp (h1 hB)).1, ((wpBranches_and bs Q R s).mp h2).1⟩,
           ⟨fun hB => ((wp_and S Q R s).mp (h1 hB)).2, ((wpBranches_and bs Q R s).mp h2).2⟩⟩,
       fun ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ =>
          ⟨fun hB => (wp_and S Q R s).mpr ⟨h1 hB, h3 hB⟩,
           (wpBranches_and bs Q R s).mpr ⟨h2, h4⟩⟩⟩
end

-- 6.1
theorem ExcludedMiracle (S : Cmd St) (s : St) : wp S (fun _ => F) s ↔ F := wp_miracle S s
-- 6.2
theorem DistributivityOfConjunction (S : Cmd St) (Q R : Pred St) (s : St) :
    wp S (fun s => Q s ∧ R s) s ↔ wp S Q s ∧ wp S R s := wp_and S Q R s
-- Monotonicity requires `Q ⇒ R` in every state.
theorem Monotonicity (S : Cmd St) (Q R : Pred St) (s : St) :
    (∀ s, Q s ⇒ R s) → (wp S Q s ⇒ wp S R s) := fun h => wp_mono S Q R h s
-- 6.4
theorem DistributivityOfDisjunction (S : Cmd St) (Q R : Pred St) (s : St) :
    wp S Q s ∨ wp S R s ⇒ wp S (fun s => Q s ∨ R s) s := fun h =>
  h.elim (wp_mono S Q (fun s => Q s ∨ R s) (fun _ hq => Or.inl hq) s)
    (wp_mono S R (fun s => Q s ∨ R s) (fun _ hr => Or.inr hr) s)

/-! ## The commands (§7–§11) -/

-- 7.1
theorem DefinitionOfSkip (R : Pred St) (s : St) : wp .skip R s ↔ R s := Iff.rfl
-- 8.1
theorem DefinitionOfAbort (R : Pred St) (s : St) : wp .abort R s ↔ F := Iff.rfl
-- 9.1
theorem DefinitionOfSequentialComposition (S₁ S₂ : Cmd St) (R : Pred St) (s : St) :
    wp (.seq S₁ S₂) R s ↔ wp S₁ (wp S₂ R) s := Iff.rfl
-- 10.1, 10.2
theorem DefinitionOfAssignment (f : St → St) (R : Pred St) (s : St) :
    wp (.assign f) R s ↔ R (f s) := Iff.rfl
-- 11.2
theorem DefinitionOfIF.l1 (B₁ : Pred St) (S₁ : Cmd St) (R : Pred St) (s : St) :
    wp (.ifc [(B₁, S₁)]) R s ↔ B₁ s ∧ (B₁ s ⇒ wp S₁ R s) := by
  simp only [wp, wpBranches, bb, F_def, T_def, or_false, and_true]
theorem DefinitionOfIF.l2 (B₁ B₂ : Pred St) (S₁ S₂ : Cmd St) (R : Pred St) (s : St) :
    wp (.ifc [(B₁, S₁), (B₂, S₂)]) R s ↔
      (B₁ s ∨ B₂ s) ∧ (B₁ s ⇒ wp S₁ R s) ∧ (B₂ s ⇒ wp S₂ R s) := by
  simp only [wp, wpBranches, bb, F_def, T_def, or_false, and_true]
theorem DefinitionOfIF.l3 (B₁ B₂ B₃ : Pred St) (S₁ S₂ S₃ : Cmd St) (R : Pred St) (s : St) :
    wp (.ifc [(B₁, S₁), (B₂, S₂), (B₃, S₃)]) R s ↔
      (B₁ s ∨ B₂ s ∨ B₃ s) ∧ (B₁ s ⇒ wp S₁ R s) ∧ (B₂ s ⇒ wp S₂ R s) ∧ (B₃ s ⇒ wp S₃ R s) := by
  simp only [wp, wpBranches, bb, F_def, T_def, or_false, and_true]

-- Unfold commands only through a cited definition, not during unification.
attribute [irreducible] wp wpBranches bb

end PT
