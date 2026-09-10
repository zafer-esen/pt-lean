import PT.Axioms

namespace PT

private theorem eqT {p : Prop} (hp : p) : p = T := propext ⟨fun _ => T.intro, fun _ => hp⟩
private theorem eqF {p : Prop} (hnp : ¬p) : p = F := propext ⟨fun hp => (hnp hp).elim, fun h => h.elim'⟩

/-! ### Equivalence and Truth -/
theorem AssociativityOfEq (p q r : Prop) : ((p ↔ q) ↔ r) ↔ (p ↔ (q ↔ r)) := by truth_table p q r
theorem IdentityOfEq (p : Prop) : (T ↔ p) ↔ p := by truth_table p
theorem Truth : T := T.intro

/-! ### Negation, Inequivalence, and False -/
theorem DefinitionOfF : F ↔ ¬T := by truth_table
theorem DistributivityOfNotOverEq.l1 (p q : Prop) : ¬(p ↔ q) ↔ (¬p ↔ q) := by truth_table p q
theorem DistributivityOfNotOverEq.l2 (p q : Prop) : (¬p ↔ q) ↔ (p ↔ ¬q) := by truth_table p q
theorem NegationOfF : ¬F ↔ T := by truth_table
theorem DefinitionOfNot.l1 (p : Prop) : (¬p ↔ p) ↔ F := by truth_table p
theorem DefinitionOfNot.l2 (p : Prop) : ¬p ↔ (p ↔ F) := by truth_table p

/-! ### Disjunction -/
theorem DistributivityOfOrOverEq.l1 (p q r : Prop) : p ∨ (q ↔ r) ↔ ((p ∨ q) ↔ (p ∨ r)) := by truth_table p q r
theorem DistributivityOfOrOverEq.l2 (p q r : Prop) : ((p ∨ (q ↔ r)) ↔ (p ∨ q)) ↔ (p ∨ r) := by truth_table p q r
theorem DistributivityOfOrOverOr (p q r : Prop) : p ∨ (q ∨ r) ↔ (p ∨ q) ∨ (p ∨ r) := by truth_table p q r

/-! ### Conjunction -/
theorem MutualDefinition.l1 (p q : Prop) : p ∧ q ↔ (p ↔ (q ↔ (p ∨ q))) := by truth_table p q
theorem MutualDefinition.l2 (p q : Prop) : p ∧ q ↔ ((p ↔ q) ↔ (p ∨ q)) := by truth_table p q
theorem MutualDefinition.l3 (p q : Prop) : ((p ∧ q) ↔ p) ↔ (q ↔ (p ∨ q)) := by truth_table p q
theorem MutualDefinition.l4 (p q : Prop) : ((p ∧ q) ↔ (p ↔ q)) ↔ (p ∨ q) := by truth_table p q
theorem MutualDefinition.l5 (p q : Prop) : (((p ∧ q) ↔ p) ↔ q) ↔ (p ∨ q) := by truth_table p q
theorem DistributivityOfAndOverAnd (p q r : Prop) : p ∧ (q ∧ r) ↔ (p ∧ q) ∧ (p ∧ r) := by truth_table p q r
theorem Absorption.l1 (p q : Prop) : p ∧ (¬p ∨ q) ↔ p ∧ q := by truth_table p q
theorem Absorption.l2 (p q : Prop) : p ∨ (¬p ∧ q) ↔ p ∨ q := by truth_table p q
theorem DistributivityOfAndOverEq.l1 (p q : Prop) : p ∧ q ↔ ((p ∧ ¬q) ↔ ¬p) := by truth_table p q
theorem DistributivityOfAndOverEq.l2 (p q : Prop) : ((p ∧ q) ↔ (p ∧ ¬q)) ↔ ¬p := by truth_table p q
theorem DistributivityOfAndOverEq.l3 (p q : Prop) : p ∧ (q ↔ p) ↔ p ∧ q := by truth_table p q
theorem Replacement (p q r : Prop) : (p ↔ q) ∧ (r ↔ p) ↔ (p ↔ q) ∧ (r ↔ q) := by truth_table p q r
theorem DefinitionOfEq (p q : Prop) : (p ↔ q) ↔ (p ∧ q) ∨ (¬p ∧ ¬q) := by truth_table p q
theorem ExclusiveOr (p q : Prop) : ¬(p ↔ q) ↔ (¬p ∧ q) ∨ (p ∧ ¬q) := by truth_table p q

/-! ### Implication -/
theorem DefinitionOfImplication.l1 (p q : Prop) : (p ⇒ q) ↔ ((p ∨ q) ↔ q) := by truth_table p q
theorem DefinitionOfImplication.l2 (p q : Prop) : ((p ⇒ q) ↔ (p ∨ q)) ↔ q := by truth_table p q
theorem DefinitionOfImplication.l3 (p q : Prop) : (p ⇒ q) ↔ ((p ∧ q) ↔ p) := by truth_table p q
theorem DefinitionOfImplication.l4 (p q : Prop) : ((p ⇒ q) ↔ (p ∧ q)) ↔ p := by truth_table p q
theorem Contrapositive (p q : Prop) : (p ⇒ q) ↔ (¬q ⇒ ¬p) := by truth_table p q
theorem DistributivityOfImpOverEq (p q r : Prop) : (p ⇒ (q ↔ r)) ↔ ((p ⇒ q) ↔ (p ⇒ r)) := by truth_table p q r
theorem Shunting (p q r : Prop) : (p ∧ q ⇒ r) ↔ (p ⇒ (q ⇒ r)) := by truth_table p q r
theorem EliminationIntroduction.l1 (p q : Prop) : p ∧ (p ⇒ q) ↔ p ∧ q := by truth_table p q
theorem EliminationIntroduction.l2 (p q : Prop) : p ∧ (q ⇒ p) ↔ p := by truth_table p q
theorem EliminationIntroduction.l3 (p q : Prop) : p ∨ (p ⇒ q) ↔ T := by truth_table p q
theorem EliminationIntroduction.l4 (p q : Prop) : p ∨ (q ⇒ p) ↔ ¬q ∨ p := by truth_table p q
theorem EliminationIntroduction.l5 (p q : Prop) : ((p ∨ q) ⇒ (p ∧ q)) ↔ (p ↔ q) := by truth_table p q
theorem EliminationIntroduction.l6 (p : Prop) : (p ⇒ F) ↔ ¬p := by truth_table p
theorem EliminationIntroduction.l7 (p : Prop) : (F ⇒ p) ↔ T := by truth_table p
theorem RightZeroOfImp (p : Prop) : (p ⇒ T) ↔ T := by truth_table p
theorem LeftIdentityOfImp (p : Prop) : (T ⇒ p) ↔ p := by truth_table p
theorem Weakening.l1 (p q : Prop) : p ⇒ p ∨ q := by truth_table p q
theorem Weakening.l2 (p q : Prop) : p ∧ q ⇒ p := by truth_table p q
theorem Weakening.l3 (p q : Prop) : p ∧ q ⇒ p ∨ q := by truth_table p q
theorem Weakening.l4 (p q r : Prop) : p ∨ (q ∧ r) ⇒ p ∨ q := by truth_table p q r
theorem Weakening.l5 (p q r : Prop) : p ∧ q ⇒ p ∧ (q ∨ r) := by truth_table p q r
theorem ModusPonens (p q : Prop) : p ∧ (p ⇒ q) ⇒ q := by truth_table p q
theorem ProofByCases.l1 (p q r : Prop) : (p ⇒ r) ∧ (q ⇒ r) ↔ (p ∨ q ⇒ r) := by truth_table p q r
theorem ProofByCases.l2 (p r : Prop) : (p ⇒ r) ∧ (¬p ⇒ r) ↔ r := by truth_table p r
theorem MutualImplication (p q : Prop) : (p ⇒ q) ∧ (q ⇒ p) ↔ (p ↔ q) := by truth_table p q
theorem Antisymmetry (p q : Prop) : (p ⇒ q) ∧ (q ⇒ p) ⇒ (p ↔ q) := by truth_table p q
theorem Transitivity.l1 (p q r : Prop) : (p ⇒ q) ∧ (q ⇒ r) ⇒ (p ⇒ r) := by truth_table p q r
theorem Transitivity.l2 (p q r : Prop) : (p ↔ q) ∧ (q ⇒ r) ⇒ (p ⇒ r) := by truth_table p q r
theorem Transitivity.l3 (p q r : Prop) : (p ⇒ q) ∧ (q ↔ r) ⇒ (p ⇒ r) := by truth_table p q r
theorem MonotonicityOfOr (p q r : Prop) : (p ⇒ q) ⇒ (p ∨ r ⇒ q ∨ r) := by truth_table p q r
theorem MonotonicityOfAnd (p q r : Prop) : (p ⇒ q) ⇒ (p ∧ r ⇒ q ∧ r) := by truth_table p q r

/-! ### Substitution (schemas in a context `E`) -/
theorem Leibniz (e f : Prop) (E : Prop → Prop) : (e ↔ f) ⇒ (E e ↔ E f) :=
  fun h => (congrArg E (propext h)) ▸ Iff.rfl
theorem Substitution.l1 (e f : Prop) (E : Prop → Prop) : (e ↔ f) ∧ E e ↔ (e ↔ f) ∧ E f :=
  ⟨fun ⟨h, he⟩ => ⟨h, (congrArg E (propext h)).mp he⟩, fun ⟨h, hf⟩ => ⟨h, (congrArg E (propext h)).mpr hf⟩⟩
theorem Substitution.l2 (e f : Prop) (E : Prop → Prop) : ((e ↔ f) ⇒ E e) ↔ ((e ↔ f) ⇒ E f) := by
  simp only [Imp_def]
  exact ⟨fun g h => (congrArg E (propext h)).mp (g h), fun g h => (congrArg E (propext h)).mpr (g h)⟩
theorem Substitution.l3 (q e f : Prop) (E : Prop → Prop) : (q ∧ (e ↔ f) ⇒ E e) ↔ (q ∧ (e ↔ f) ⇒ E f) := by
  simp only [Imp_def]
  exact ⟨fun g ⟨hq, h⟩ => (congrArg E (propext h)).mp (g ⟨hq, h⟩),
         fun g ⟨hq, h⟩ => (congrArg E (propext h)).mpr (g ⟨hq, h⟩)⟩
-- the same for integer expressions (`(i = j) ∧ P(i) = (i = j) ∧ P(j)`)
theorem Leibniz.i (e f : Int) (E : Int → Prop) : (e = f) ⇒ (E e ↔ E f) :=
  fun h => by subst h; exact Iff.rfl
theorem Substitution.i1 (e f : Int) (E : Int → Prop) : (e = f) ∧ E e ↔ (e = f) ∧ E f :=
  ⟨fun ⟨h, he⟩ => ⟨h, by subst h; exact he⟩, fun ⟨h, hf⟩ => ⟨h, by subst h; exact hf⟩⟩
theorem Substitution.i2 (e f : Int) (E : Int → Prop) : ((e = f) ⇒ E e) ↔ ((e = f) ⇒ E f) := by
  simp only [Imp_def]
  exact ⟨fun g h => by subst h; exact g rfl, fun g h => by subst h; exact g rfl⟩
theorem Substitution.i3 (q : Prop) (e f : Int) (E : Int → Prop) :
    (q ∧ (e = f) ⇒ E e) ↔ (q ∧ (e = f) ⇒ E f) := by
  simp only [Imp_def]
  exact ⟨fun g ⟨hq, h⟩ => by subst h; exact g ⟨hq, rfl⟩, fun g ⟨hq, h⟩ => by subst h; exact g ⟨hq, rfl⟩⟩
theorem ReplaceByT.l1 (p : Prop) (E : Prop → Prop) : p ∧ E p ↔ p ∧ E T :=
  ⟨fun ⟨hp, h⟩ => ⟨hp, (congrArg E (eqT hp)).mp h⟩, fun ⟨hp, h⟩ => ⟨hp, (congrArg E (eqT hp)).mpr h⟩⟩
theorem ReplaceByT.l2 (p : Prop) (E : Prop → Prop) : (p ⇒ E p) ↔ (p ⇒ E T) := by
  simp only [Imp_def]
  exact ⟨fun g hp => (congrArg E (eqT hp)).mp (g hp), fun g hp => (congrArg E (eqT hp)).mpr (g hp)⟩
theorem ReplaceByT.l3 (q p : Prop) (E : Prop → Prop) : (q ∧ p ⇒ E p) ↔ (q ∧ p ⇒ E T) := by
  simp only [Imp_def]
  exact ⟨fun g ⟨hq, hp⟩ => (congrArg E (eqT hp)).mp (g ⟨hq, hp⟩),
         fun g ⟨hq, hp⟩ => (congrArg E (eqT hp)).mpr (g ⟨hq, hp⟩)⟩
theorem ReplaceByF.l1 (p : Prop) (E : Prop → Prop) : p ∨ E p ↔ p ∨ E F :=
  ⟨fun h => h.elim Or.inl (fun he => Classical.byCases (fun hp : p => Or.inl hp)
      (fun hnp => Or.inr ((congrArg E (eqF hnp)).mp he))),
   fun h => h.elim Or.inl (fun hf => Classical.byCases (fun hp : p => Or.inl hp)
      (fun hnp => Or.inr ((congrArg E (eqF hnp)).mpr hf)))⟩
theorem ReplaceByF.l2 (p : Prop) (E : Prop → Prop) : (E p ⇒ p) ↔ (E F ⇒ p) := by
  simp only [Imp_def]
  exact ⟨fun g hf => Classical.byCases (fun hp : p => hp) (fun hnp => g ((congrArg E (eqF hnp)).mpr hf)),
         fun g he => Classical.byCases (fun hp : p => hp) (fun hnp => g ((congrArg E (eqF hnp)).mp he))⟩
theorem ReplaceByF.l3 (p q : Prop) (E : Prop → Prop) : (E p ⇒ p ∨ q) ↔ (E F ⇒ p ∨ q) := by
  simp only [Imp_def]
  exact ⟨fun g hf => Classical.byCases (fun hp : p => Or.inl hp) (fun hnp => g ((congrArg E (eqF hnp)).mpr hf)),
         fun g he => Classical.byCases (fun hp : p => Or.inl hp) (fun hnp => g ((congrArg E (eqF hnp)).mp he))⟩
theorem Shannon (p : Prop) (E : Prop → Prop) : E p ↔ (p ∧ E T) ∨ (¬p ∧ E F) :=
  ⟨fun he => Classical.byCases (fun hp : p => Or.inl ⟨hp, (congrArg E (eqT hp)).mp he⟩)
      (fun hnp => Or.inr ⟨hnp, (congrArg E (eqF hnp)).mp he⟩),
   fun h => h.elim (fun ⟨hp, ht⟩ => (congrArg E (eqT hp)).mpr ht) (fun ⟨hnp, hf⟩ => (congrArg E (eqF hnp)).mpr hf)⟩

end PT
