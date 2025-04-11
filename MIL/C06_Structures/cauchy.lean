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

theorem test123 (p : ℕ) (hp: Nat.Prime p) :
  p ≥ 0 := by

  let X := {x : Vector ℕ p | p ≥ 0}

  have : NeZero p := by
    constructor

    apply Nat.Prime.ne_zero at hp -- gives hp : p ≠ 0
    --exact hp doesn't work here, for example (neither does simp, linarith)
    sorry

  have : ∀ x ∈ X, x.head ≥ 0 := by
    sorry


theorem test1231 (p : ℕ) (hp: Nat.Prime p) :
  p ≥ 0 := by

  let X := {x : Vector ℕ p | p ≥ 0}

  have : ∀ x ∈ X, x.head ≥ 0 := by
    sorry

lemma fold_identa {G: Type*} [Group G] {p : ℕ} [NeZero p] (hp : p ≥ 1) (x : List G) (g : G) (f : G → G → G) :
  f (x.dropLast.foldl f 1) g = x.foldl f 1 := by

  have : x = x.dropLast ++ [g] := by sorry
  nth_rw 2 [this]
  rw[List.foldl_concat f 1 g x.dropLast]

lemma fold_identb {G: Type*} [Group G] {p : ℕ} [NeZero p] (hp : p ≥ 1) (x : Vector G p) (g : G) (f : G → G → G) :
  f (x.pop.foldl f 1) x.back = x.foldl f 1 := by

  let xl := x.toList
  let xlm := x.pop.toList

  --have : xl = xl.dropLast ++ [xl.getLast] := by
  --  symm
  --  apply List.dropLast_append_getLast

  have : xl ≠ [] := by sorry
  have lem : x.back = xl.getLast this := by
    sorry

  have : xl = xl.dropLast ++ [x.back] := by
    rw [lem]
    rw [List.dropLast_append_getLast this]


  rw [← List.dropLast_append_getLast]
  rw[List.foldl_concat f 1 g x.dropLast]

lemma fold_ident {G: Type*} [Group G] {p : ℕ} [NeZero p] (hp : p ≥ 1) (x : Vector G p) (f : G → G → G) :
  f (x.pop.foldl f 1) x.back = x.foldl f 1 := by

  --rw [← List.head_eq_getElem_zero]
  --simp

  have : ∃ m : ℕ, p = m + 1 := by
    cases p with
    | zero => contradiction
    | succ n => simp

  rcases this with ⟨m, hpm⟩
  rw [List.foldl_concat]



  sorry

lemma fold_ident {G: Type*} [Group G] {p : ℕ} [NeZero p] (hp : p ≥ 1) (x : Vector G p) (f : G → G → G) :
  f x.head (x.tail.foldl f 1) = x.foldl f 1 := by
  simp
  rw [Equiv.arrayEquivList]
  rw [← List.cons_head?_tail]


lemma fold_ident {G: Type*} [Group G] {p : ℕ} [NeZero p] (hp : p ≥ 1) (x : Vector G p) :
  x.head * x.tail.foldl Mul.mul 1 = x.foldl Mul.mul 1 := by
  --simp


  cases p

  contradiction




  induction' p with n hn
  contradiction








  sorry


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
