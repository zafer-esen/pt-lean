import PT.Quantifiers

namespace PT

-- 3.1
theorem DefinitionOfExists.l1 (m n : Int) (p : Int → Prop) :
    m ≥ n → ((∃ i : m ≤ i < n : p i) ↔ F) := by
  intro h
  simp only [Ex, F_def]
  constructor
  · rintro ⟨i, ⟨h₁, h₂⟩, -⟩; omega
  · exact False.elim
theorem DefinitionOfExists.l2 (m n : Int) (p : Int → Prop) :
    m < n → ((∃ i : m ≤ i < n : p i) ↔ (∃ i : m ≤ i < n - 1 : p i) ∨ p (n - 1)) := by
  intro h
  simp only [Ex]
  constructor
  · rintro ⟨i, ⟨h₁, h₂⟩, hp⟩
    by_cases hi : i = n - 1
    · subst hi; exact Or.inr hp
    · exact Or.inl ⟨i, ⟨h₁, by omega⟩, hp⟩
  · rintro (⟨i, ⟨h₁, h₂⟩, hp⟩ | hp)
    · exact ⟨i, ⟨h₁, by omega⟩, hp⟩
    · exact ⟨n - 1, ⟨by omega, by omega⟩, hp⟩
-- 3.2
theorem DefinitionOfForall.l1 (m n : Int) (p : Int → Prop) :
    m ≥ n → ((∀ i : m ≤ i < n : p i) ↔ T) := by
  intro h
  simp only [Forall, T_def]
  constructor
  · intro _; trivial
  · rintro - i ⟨h₁, h₂⟩; omega
theorem DefinitionOfForall.l2 (m n : Int) (p : Int → Prop) :
    m < n → ((∀ i : m ≤ i < n : p i) ↔ (∀ i : m ≤ i < n - 1 : p i) ∧ p (n - 1)) := by
  intro h
  simp only [Forall]
  constructor
  · intro hall
    exact ⟨fun i ⟨h₁, h₂⟩ => hall i ⟨h₁, by omega⟩, hall (n - 1) ⟨by omega, by omega⟩⟩
  · rintro ⟨hall, hlast⟩ i ⟨h₁, h₂⟩
    by_cases hi : i = n - 1
    · subst hi; exact hlast
    · exact hall i ⟨h₁, by omega⟩
-- 3.3
theorem RangeSplit.l1 (m₁ m₂ m₃ : Int) (p : Int → Prop) :
    m₁ ≤ m₂ ∧ m₂ ≤ m₃ → ((∀ i : m₁ ≤ i < m₂ : p i) ∧ (∀ i : m₂ ≤ i < m₃ : p i) ↔ (∀ i : m₁ ≤ i < m₃ : p i)) := by
  rintro ⟨h₁, h₂⟩
  simp only [Forall]
  constructor
  · rintro ⟨hlo, hhi⟩ i ⟨ha, hb⟩
    by_cases hi : i < m₂
    · exact hlo i ⟨ha, hi⟩
    · exact hhi i ⟨by omega, hb⟩
  · intro h
    exact ⟨fun i ⟨ha, hb⟩ => h i ⟨ha, by omega⟩, fun i ⟨ha, hb⟩ => h i ⟨by omega, hb⟩⟩
theorem RangeSplit.l2 (m₁ m₂ n₁ n₂ : Int) (p : Int → Prop) :
    m₁ ≤ m₂ ∧ n₁ ≥ n₂ → ((∀ i : m₁ ≤ i < n₁ : p i) ∧ (∀ i : m₂ ≤ i < n₂ : p i) ↔ (∀ i : m₁ ≤ i < n₁ : p i)) := by
  rintro ⟨h₁, h₂⟩
  simp only [Forall]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun i ⟨ha, hb⟩ => h i ⟨by omega, by omega⟩⟩
theorem RangeSplit.l3 (m₁ m₂ m₃ : Int) (p : Int → Prop) :
    m₁ ≤ m₂ ∧ m₂ ≤ m₃ → ((∃ i : m₁ ≤ i < m₂ : p i) ∨ (∃ i : m₂ ≤ i < m₃ : p i) ↔ (∃ i : m₁ ≤ i < m₃ : p i)) := by
  rintro ⟨h₁, h₂⟩
  simp only [Ex]
  constructor
  · rintro (⟨i, ⟨ha, hb⟩, hp⟩ | ⟨i, ⟨ha, hb⟩, hp⟩) <;> exact ⟨i, ⟨by omega, by omega⟩, hp⟩
  · rintro ⟨i, ⟨ha, hb⟩, hp⟩
    by_cases hi : i < m₂
    · exact Or.inl ⟨i, ⟨ha, hi⟩, hp⟩
    · exact Or.inr ⟨i, ⟨by omega, hb⟩, hp⟩
theorem RangeSplit.l4 (m₁ m₂ n₁ n₂ : Int) (p : Int → Prop) :
    m₁ ≤ m₂ ∧ n₁ ≥ n₂ → ((∃ i : m₁ ≤ i < n₁ : p i) ∨ (∃ i : m₂ ≤ i < n₂ : p i) ↔ (∃ i : m₁ ≤ i < n₁ : p i)) := by
  rintro ⟨h₁, h₂⟩
  simp only [Ex]
  constructor
  · rintro (h | ⟨i, ⟨ha, hb⟩, hp⟩)
    · exact h
    · exact ⟨i, ⟨by omega, by omega⟩, hp⟩
  · exact Or.inl
private theorem Summation.go_add (m : Int) (e : Int → Int) (a b : Nat) :
    Summation.go m e (a + b) = Summation.go m e a + Summation.go (m + a) e b := by
  induction b with
  | zero => simp [Summation.go]
  | succ k ih =>
    have hc : ((a + k : Nat) : Int) = (a : Int) + k := by omega
    show Summation.go m e (a + k) + e (m + ((a + k : Nat) : Int)) = _
    show _ = Summation.go m e a + (Summation.go (m + a) e k + e (m + (a : Int) + k))
    rw [ih, hc, ← Int.add_assoc, Int.add_assoc]
private theorem Product.go_add (m : Int) (e : Int → Int) (a b : Nat) :
    Product.go m e (a + b) = Product.go m e a * Product.go (m + a) e b := by
  induction b with
  | zero => simp [Product.go]
  | succ k ih =>
    have hc : ((a + k : Nat) : Int) = (a : Int) + k := by omega
    show Product.go m e (a + k) * e (m + ((a + k : Nat) : Int)) = _
    show _ = Product.go m e a * (Product.go (m + a) e k * e (m + (a : Int) + k))
    rw [ih, hc, ← Int.add_assoc, Int.mul_assoc]
theorem RangeSplit.l5 (m₁ m₂ m₃ : Int) (p : Int → Prop) :
    m₁ ≤ m₂ ∧ m₂ ≤ m₃ → Count m₁ m₂ p + Count m₂ m₃ p = Count m₁ m₃ p := by
  rintro ⟨h₁, h₂⟩
  unfold Count Summation
  rw [show (m₃ - m₁).toNat = (m₂ - m₁).toNat + (m₃ - m₂).toNat by omega,
      Summation.go_add, show m₁ + ((m₂ - m₁).toNat : Int) = m₂ by omega]
theorem RangeSplit.l6 (m₁ m₂ m₃ : Int) (e : Int → Int) :
    m₁ ≤ m₂ ∧ m₂ ≤ m₃ → (Σ i : m₁ ≤ i < m₂ : e i) + (Σ i : m₂ ≤ i < m₃ : e i) = (Σ i : m₁ ≤ i < m₃ : e i) := by
  rintro ⟨h₁, h₂⟩
  unfold Summation
  rw [show (m₃ - m₁).toNat = (m₂ - m₁).toNat + (m₃ - m₂).toNat by omega,
      Summation.go_add, show m₁ + ((m₂ - m₁).toNat : Int) = m₂ by omega]
theorem RangeSplit.l7 (m₁ m₂ m₃ : Int) (e : Int → Int) :
    m₁ ≤ m₂ ∧ m₂ ≤ m₃ → (Π i : m₁ ≤ i < m₂ : e i) * (Π i : m₂ ≤ i < m₃ : e i) = (Π i : m₁ ≤ i < m₃ : e i) := by
  rintro ⟨h₁, h₂⟩
  unfold Product
  rw [show (m₃ - m₁).toNat = (m₂ - m₁).toNat + (m₃ - m₂).toNat by omega,
      Product.go_add, show m₁ + ((m₂ - m₁).toNat : Int) = m₂ by omega]
-- 3.4
theorem InterchangeOfDummies.l1 (m₁ n₁ m₂ n₂ : Int) (p : Int → Int → Prop) :
    (∀ i : m₁ ≤ i < n₁ : (∀ j : m₂ ≤ j < n₂ : p i j)) ↔ (∀ j : m₂ ≤ j < n₂ : (∀ i : m₁ ≤ i < n₁ : p i j)) := by
  simp only [Forall]
  exact ⟨fun h j hj i hi => h i hi j hj, fun h i hi j hj => h j hj i hi⟩
theorem InterchangeOfDummies.l2 (m₁ n₁ m₂ n₂ : Int) (p : Int → Int → Prop) :
    (∃ i : m₁ ≤ i < n₁ : (∃ j : m₂ ≤ j < n₂ : p i j)) ↔ (∃ j : m₂ ≤ j < n₂ : (∃ i : m₁ ≤ i < n₁ : p i j)) := by
  simp only [Ex]
  constructor
  · rintro ⟨i, hi, j, hj, hp⟩; exact ⟨j, hj, i, hi, hp⟩
  · rintro ⟨j, hj, i, hi, hp⟩; exact ⟨i, hi, j, hj, hp⟩
-- 3.5  Lean treats formulas differing only in bound variable names as equal.
theorem DummyRenaming.l1 (m n : Int) (p : Int → Prop) :
    (∀ i : m ≤ i < n : p i) ↔ (∀ j : m ≤ j < n : p j) := Iff.rfl
theorem DummyRenaming.l2 (m n : Int) (p : Int → Prop) :
    (∃ i : m ≤ i < n : p i) ↔ (∃ j : m ≤ j < n : p j) := Iff.rfl
-- 3.6
theorem DistributivityOfOrOverForall (p : Prop) (m n : Int) (q : Int → Prop) :
    p ∨ (∀ i : m ≤ i < n : q i) ↔ (∀ i : m ≤ i < n : p ∨ q i) := by
  simp only [Forall]
  constructor
  · rintro (hp | h) i hi
    · exact Or.inl hp
    · exact Or.inr (h i hi)
  · intro h
    by_cases hp : p
    · exact Or.inl hp
    · exact Or.inr fun i hi => (h i hi).resolve_left hp
-- 3.7
theorem DistributivityOfAndOverForall.l1 (p : Prop) (m n : Int) (q : Int → Prop) :
    m < n → (p ∧ (∀ i : m ≤ i < n : q i) ↔ (∀ i : m ≤ i < n : p ∧ q i)) := by
  intro h
  simp only [Forall]
  constructor
  · rintro ⟨hp, hq⟩ i hi; exact ⟨hp, hq i hi⟩
  · intro hall
    exact ⟨(hall m ⟨by omega, h⟩).1, fun i hi => (hall i hi).2⟩
theorem DistributivityOfAndOverForall.l2 (m n : Int) (p q : Int → Prop) :
    (∀ i : m ≤ i < n : p i) ∧ (∀ i : m ≤ i < n : q i) ↔ (∀ i : m ≤ i < n : p i ∧ q i) := by
  simp only [Forall]
  constructor
  · rintro ⟨hp, hq⟩ i hi; exact ⟨hp i hi, hq i hi⟩
  · intro h
    exact ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩
-- 3.8
theorem DistributivityOfAndOverExists (p : Prop) (m n : Int) (q : Int → Prop) :
    p ∧ (∃ i : m ≤ i < n : q i) ↔ (∃ i : m ≤ i < n : p ∧ q i) := by
  simp only [Ex]
  constructor
  · rintro ⟨hp, i, hi, hq⟩; exact ⟨i, hi, hp, hq⟩
  · rintro ⟨i, hi, hp, hq⟩; exact ⟨hp, i, hi, hq⟩
-- 3.9
theorem DistributivityOfOrOverExists.l1 (p : Prop) (m n : Int) (q : Int → Prop) :
    m < n → (p ∨ (∃ i : m ≤ i < n : q i) ↔ (∃ i : m ≤ i < n : p ∨ q i)) := by
  intro h
  simp only [Ex]
  constructor
  · rintro (hp | ⟨i, hi, hq⟩)
    · exact ⟨m, ⟨by omega, h⟩, Or.inl hp⟩
    · exact ⟨i, hi, Or.inr hq⟩
  · rintro ⟨i, hi, (hp | hq)⟩
    · exact Or.inl hp
    · exact Or.inr ⟨i, hi, hq⟩
theorem DistributivityOfOrOverExists.l2 (m n : Int) (p q : Int → Prop) :
    (∃ i : m ≤ i < n : p i) ∨ (∃ i : m ≤ i < n : q i) ↔ (∃ i : m ≤ i < n : p i ∨ q i) := by
  simp only [Ex]
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, hi, Or.inl h⟩
    · exact ⟨i, hi, Or.inr h⟩
  · rintro ⟨i, hi, (h | h)⟩
    · exact Or.inl ⟨i, hi, h⟩
    · exact Or.inr ⟨i, hi, h⟩
-- 3.10
theorem UniversalityOfT (m n : Int) : (∀ i : m ≤ i < n : T) ↔ T := by
  simp only [Forall, T_def]
  exact ⟨fun _ => trivial, fun _ _ _ => trivial⟩
-- 3.11
theorem ExistenceOfF (m n : Int) : (∃ i : m ≤ i < n : F) ↔ F := by
  simp only [Ex, F_def]
  exact ⟨fun ⟨_, _, h⟩ => h, False.elim⟩
-- 3.12
theorem GeneralizedDeMorgan.l1 (m n : Int) (p : Int → Prop) :
    ¬ (∃ i : m ≤ i < n : p i) ↔ (∀ i : m ≤ i < n : ¬ p i) := by
  simp only [Forall, Ex]
  constructor
  · intro h i hi hp; exact h ⟨i, hi, hp⟩
  · rintro h ⟨i, hi, hp⟩; exact h i hi hp
theorem GeneralizedDeMorgan.l2 (m n : Int) (p : Int → Prop) :
    ¬ (∀ i : m ≤ i < n : p i) ↔ (∃ i : m ≤ i < n : ¬ p i) := by
  simp only [Forall, Ex]
  constructor
  · intro h
    refine Classical.byContradiction fun hc => h ?_
    intro i hi
    exact Classical.byContradiction fun hp => hc ⟨i, hi, hp⟩
  · rintro ⟨i, hi, hp⟩ h; exact hp (h i hi)
-- 3.13  (for a fixed `i`, where the appendix's `=` holds under a universal closure of `i`)
theorem Trading.l1 (m n i : Int) (p : Int → Prop) :
    (∀ j : m ≤ j < n : p j) ⇒ ((m ≤ i < n) ⇒ p i) := fun h hi => h i hi
theorem Trading.l2 (m n i : Int) (p : Int → Prop) :
    ((m ≤ i < n) ∧ p i) ⇒ (∃ j : m ≤ j < n : p j) := fun ⟨hi, hp⟩ => ⟨i, hi, hp⟩
-- 3.14
theorem DefinitionOfCount.l1 (m n : Int) (p : Int → Prop) :
    m ≥ n → Count m n p = 0 := by
  intro h
  unfold Count Summation
  rw [show (n - m).toNat = 0 by omega]
  rfl
theorem DefinitionOfCount.l2 (m n : Int) (p : Int → Prop) :
    m < n ∧ ¬ p (n - 1) → Count m n p = Count m (n - 1) p := by
  rintro ⟨h, hp⟩
  have hk : (n - m).toNat = (n - 1 - m).toNat + 1 := by omega
  have hm : m + ((n - 1 - m).toNat : Int) = n - 1 := by omega
  unfold Count Summation
  rw [hk]
  simp only [Summation.go]
  rw [hm, if_neg hp, Int.add_zero]
theorem DefinitionOfCount.l3 (m n : Int) (p : Int → Prop) :
    m < n ∧ p (n - 1) → Count m n p = Count m (n - 1) p + 1 := by
  rintro ⟨h, hp⟩
  have hk : (n - m).toNat = (n - 1 - m).toNat + 1 := by omega
  have hm : m + ((n - 1 - m).toNat : Int) = n - 1 := by omega
  unfold Count Summation
  rw [hk]
  simp only [Summation.go]
  rw [hm, if_pos hp]
-- 3.15
theorem DefinitionOfSum.l1 (m n : Int) (e : Int → Int) :
    m ≥ n → (Σ i : m ≤ i < n : e i) = 0 := by
  intro h
  unfold Summation
  rw [show (n - m).toNat = 0 by omega]
  rfl
theorem DefinitionOfSum.l2 (m n : Int) (e : Int → Int) :
    m < n → (Σ i : m ≤ i < n : e i) = (Σ i : m ≤ i < n - 1 : e i) + e (n - 1) := by
  intro h
  have hk : (n - m).toNat = (n - 1 - m).toNat + 1 := by omega
  have hm : m + ((n - 1 - m).toNat : Int) = n - 1 := by omega
  unfold Summation
  rw [hk]
  simp only [Summation.go, hm]
-- 3.16
theorem DefinitionOfProduct.l1 (m n : Int) (e : Int → Int) :
    m ≥ n → (Π i : m ≤ i < n : e i) = 1 := by
  intro h
  unfold Product
  rw [show (n - m).toNat = 0 by omega]
  rfl
theorem DefinitionOfProduct.l2 (m n : Int) (e : Int → Int) :
    m < n → (Π i : m ≤ i < n : e i) = (Π i : m ≤ i < n - 1 : e i) * e (n - 1) := by
  intro h
  have hk : (n - m).toNat = (n - 1 - m).toNat + 1 := by omega
  have hm : m + ((n - 1 - m).toNat : Int) = n - 1 := by omega
  unfold Product
  rw [hk]
  simp only [Product.go, hm]

/-! ## Generalised definitions of `∀` and `∃` over an arbitrary range -/

theorem GeneralizedDefinitionOfForall {α : Type} (Q P : α → Prop) (c : α) :
    Q c → ((∀ x : Q x : P x) ↔ (∀ x : Q x ∧ ¬(x = c) : P x) ∧ P c) := by
  intro hc
  simp only [Forall]
  constructor
  · intro h
    exact ⟨fun x hx => h x hx.1, h c hc⟩
  · rintro ⟨h, hpc⟩ x hx
    by_cases hxc : x = c
    · subst hxc; exact hpc
    · exact h x ⟨hx, hxc⟩
theorem GeneralizedDefinitionOfExists {α : Type} (Q P : α → Prop) (c : α) :
    Q c → ((∃ x : Q x : P x) ↔ (∃ x : Q x ∧ ¬(x = c) : P x) ∨ P c) := by
  intro hc
  simp only [Ex]
  constructor
  · rintro ⟨x, hx, hp⟩
    by_cases hxc : x = c
    · subst hxc; exact Or.inr hp
    · exact Or.inl ⟨x, ⟨hx, hxc⟩, hp⟩
  · rintro (⟨x, ⟨hx, -⟩, hp⟩ | hp)
    · exact ⟨x, hx, hp⟩
    · exact ⟨c, hc, hp⟩

end PT
