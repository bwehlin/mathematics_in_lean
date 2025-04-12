import MIL.Common
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Init.Data.Vector.Basic
import Mathlib.Logic.Equiv.Array

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



-----------------

lemma fold_list {G: Type*} [Group G] (l : List G) (p : ℕ)  (hp : p > 1) (h : l.length = p) (f : G → G → G) :
  f (l.dropLast.foldl f 1) l[p-1] = l.foldl f 1 := by

  have h1 : l.length - 1 < l.length := by
    simp [hp]
    rw [h]
    linarith

  have : l ≠ [] := by
    apply List.length_pos_iff_ne_nil.mp
    linarith

  have : l[p-1] = l.getLast this := by
    symm at h
    simp [h]
    rw [←  List.get_length_sub_one h1]
    simp

  have : l = l.dropLast ++ [l[p-1]] := by
    symm
    rw [this]
    rw [List.dropLast_append_getLast]

  symm
  nth_rw 1 [this]
  rw[List.foldl_concat f 1  l[p-1] l.dropLast]



theorem Cauchy₁ {G: Type*} [Fintype G] [Group G] (p : ℕ) (hp : Nat.Prime p) (pdvd : p ∣ Fintype.card G) :
  ∃ x : G, orderOf x = p := by

  let X := { x : List G | x.length = p ∧ x.foldl Mul.mul 1 = 1}

  have xl : ∀ x ∈ X, x.length = p := by
    rintro x xmem
    simp [X, Set.mem_setOf] at xmem
    simp [xmem]

  have : ∀ x ∈ X, p - 1 < x.length := by sorry

  have pg : p > 1 := by sorry

  -- For proving x[p-1] exists: https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.E2.9C.94.20Having.20trouble.20reasoning.20about.20list.20elements
  have xmu : ∀ x, (hx : x ∈ X) → Mul.mul (x.dropLast.foldl Mul.mul 1) (x[p-1]'(this _ hx)) = 1 := by
    rintro x xmem
    simp [X, Set.mem_setOf] at xmem
    rcases xmem with ⟨xl,xmul⟩
    rw [fold_list x p pg xl Mul.mul]
    exact xmul

  -- Last element of list is inverse of product of tail
  have : ∀ x, (hx : x ∈ X) → (x[p-1]'(this _ hx))⁻¹ = x.dropLast.foldl Mul.mul 1 := by
    rintro x xmem
    rw [← one_mul (x[p-1]'(this x xmem))⁻¹]
    symm
    rw [ ← div_eq_iff_eq_mul, div_eq_mul_inv, inv_inv]
    specialize xmu x xmem
    exact xmu










theorem Cauchy₃ {G: Type*} [Fintype G] [Group G] (p : ℕ) (hp : Nat.Prime p) (pdvd : p ∣ Fintype.card G) :
  ∃ x : G, orderOf x = p := by

  let X := { x : Vector G p | x.foldl Mul.mul 1 = 1  }

  have : NeZero p := by
    -- Got some help here: https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Missing.20something.20fundamental.20about.20Props/with/511666602
    apply Nat.Prime.ne_zero at hp
    apply neZero_iff.mpr at hp
    exact hp

  have : ∀ x ∈ X, x.head * x.tail.foldl Mul.mul 1 = x.foldl Mul.mul 1 := by
    rintro x xmem
    simp



  have : ∀ x ∈ X, x.tail.foldl Mul.mul 1 = x.head⁻¹ := by
    rintro x xmem
    rw [← one_mul (x.tail.foldl Mul.mul 1)]
    nth_rw 1 [← inv_mul_cancel x.head]
    rw [mul_assoc, ← inv_inv (x.head * x.tail.foldl Mul.mul 1), mul_inv_eq_iff_eq_mul]



    symm
    rw[← div_eq_iff_eq_mul, div_eq_mul_inv, inv_inv]
    rw [← one_mul (x.tail.foldr Mul.mul 1)⁻¹, mul_assoc]

    nth_rw 1 [← inv_mul_cancel x.head]


    apply mul_eq_of_eq_mul_inv x.head 1 ((x.tail.foldr Mul.mul 1)⁻¹)
