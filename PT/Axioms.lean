import PT.Core

namespace PT

/-! ### Axiom 1.1 Commutativity -/
theorem Commutativity.and (p q : Prop) : p ∧ q ↔ q ∧ p := and_comm
theorem Commutativity.or  (p q : Prop) : p ∨ q ↔ q ∨ p := or_comm
theorem Commutativity.eq  (p q : Prop) : (p ↔ q) ↔ (q ↔ p) := ⟨Iff.symm, Iff.symm⟩

/-! ### Axiom 1.2 Associativity -/
theorem Associativity.and (p q r : Prop) : p ∧ (q ∧ r) ↔ (p ∧ q) ∧ r := and_assoc.symm
theorem Associativity.or  (p q r : Prop) : p ∨ (q ∨ r) ↔ (p ∨ q) ∨ r := or_assoc.symm

/-! ### Axiom 1.3 Distributivity -/
theorem Distributivity.or  (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := or_and_left
theorem Distributivity.and (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := and_or_left

/-! ### Axiom 1.4 De Morgan -/
theorem DeMorgan.and (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by truth_table p q
theorem DeMorgan.or  (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := not_or

/-! ### Axiom 1.5 Negation -/
theorem Negation (p : Prop) : ¬¬p ↔ p := by truth_table p

/-! ### Axiom 1.6 Excluded Middle -/
theorem ExcludedMiddle (p : Prop) : p ∨ ¬p ↔ T := by truth_table p

/-! ### Axiom 1.7 Contradiction -/
theorem Contradiction (p : Prop) : p ∧ ¬p ↔ F := by truth_table p

/-! ### Axiom 1.8 Implication -/
theorem Implication (p q : Prop) : (p ⇒ q) ↔ ¬p ∨ q := by truth_table p q

/-! ### Axiom 1.9 Equality -/
theorem Equality (p q : Prop) : (p ↔ q) ↔ (p ⇒ q) ∧ (q ⇒ p) := by truth_table p q

/-! ### Axiom 1.10 or-simplification -/
theorem OrSimplification.idem   (p : Prop)   : p ∨ p ↔ p := by truth_table p
theorem OrSimplification.true   (p : Prop)   : p ∨ T ↔ T := by truth_table p
theorem OrSimplification.false  (p : Prop)   : p ∨ F ↔ p := by truth_table p
theorem OrSimplification.absorb (p q : Prop) : p ∨ (p ∧ q) ↔ p := by truth_table p q

/-! ### Axiom 1.11 and-simplification -/
theorem AndSimplification.idem   (p : Prop)   : p ∧ p ↔ p := by truth_table p
theorem AndSimplification.true   (p : Prop)   : p ∧ T ↔ p := by truth_table p
theorem AndSimplification.false  (p : Prop)   : p ∧ F ↔ F := by truth_table p
theorem AndSimplification.absorb (p q : Prop) : p ∧ (p ∨ q) ↔ p := by truth_table p q

/-! ### Axiom 1.12 Identity -/
theorem Identity (p : Prop) : (p ↔ p) ↔ T := by truth_table p

end PT
