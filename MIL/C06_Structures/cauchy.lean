import MIL.Common
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card

#check Group

open Group

--set_option diagnostics true

lemma monoid_card_gt_zero {M : Type*} [Monoid M] [Fintype M] : Fintype.card M > 0 := by
  by_contra!
  apply Nat.le_zero.mp at this
  simp at this

lemma monoid_nempty {M : Type*} [Monoid M] [Fintype M] : Fintype.card M = 0 → False := by
  have : Fintype.card M > 0 := monoid_card_gt_zero
  intro h
  -- it is beyond me why the following works and 'contradiction' doesn't
  let n := Fintype.card M
  simp [n] at h

theorem thm123 {G : Type*} [Group G] : ∃ x : G, x * x = x := by
  use 1
  apply Monoid.one_mul

lemma abel_case {G : Type*} [Fintype G] [CommGroup G] (p n : ℕ) (hc : Fintype.card G = n) (hp : Nat.Prime p) (pdvd : p ∣ n) :
  ∃ x : G, orderOf x = p := by
  rcases pdvd with ⟨m, hdvd⟩

  have : m > 0 := by
    by_contra hm
    push_neg at hm
    apply Nat.le_zero.mp at hm
    rw [hm, mul_zero,← hc] at hdvd
    apply monoid_nempty at hdvd
    exact hdvd



  cases m
  · contradiction
  case succ m =>

  let n := Fintype.card G
  induction' m with m ih
  · sorry
  · sorry





theorem Cauchy₁ {G : Type*} [Fintype G] [Group G] (p : ℕ) (hp : Nat.Prime p) (pdvd : p ∣ Fintype.card G) :
  ∃ x : G, orderOf x = p := by

  let X := {l : List G | l.length = p ∧ l.prod = 1 }
  have : Finite X := by
    by_contra

  have : Fintype.card X = (Fintype.card G)^(p-1) := by
    sorry


  sorry
  --intro pdiv_card
  --constructor
  --sorry
