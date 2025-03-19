import MIL.Common

#check Group

open Group

theorem Cauchy₁ {G : Type*} [Group G] (p n : ℕ) (hp : Nat.Prime p) (hg : Finite G) : p ∣ Nat.card G → (∃ g : G, g^p = 1 ∧ (∀ s < p, g^s ≠ 1)) := by
  intro pdiv_card
  constructor
  sorry
