import MIL.Common
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Init.Data.Vector.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Basic

#check Group

open Group
open Function
open Set

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

lemma last_elem_eq_inv_of_prod {G: Type*} [Fintype G] [Group G] (p : ℕ) (hp : Nat.Prime p) (l : List G) (hl : l.length = p):
  l.length = p ∧ l.foldl Mul.mul 1 = 1 → (l[p-1]'(by simp[hl]; linarith[Nat.Prime.one_lt hp]))⁻¹ = l.dropLast.foldl Mul.mul 1 := by

  rintro ⟨_, h⟩

  have pg : p > 1 := Nat.Prime.one_lt hp
  have hl₁ : p - 1 < l.length := by
    simp[hl]
    linarith[Nat.Prime.one_lt hp]

  have xmu : Mul.mul (l.dropLast.foldl Mul.mul 1) (l[p-1]'hl₁) = 1 := by
    rw [fold_list l p pg hl Mul.mul]
    exact h

  rw [← one_mul (l[p-1]'hl₁)⁻¹]
  symm
  rw [ ← div_eq_iff_eq_mul, div_eq_mul_inv, inv_inv]
  exact xmu

variable (G : Type*) [Group G]
variable (p : ℕ) (h: Nat.Prime p)
def X : Set (List G) := { x : List G | x.length = p ∧ x.foldl Mul.mul 1 = 1}

lemma asdf : Fintype X := by


lemma mylemma {α : Type*} [Fintype α] (n : ℕ) (S : Set (List α) := {l : List α | l.length = n}) [Fintype S] :
  Fintype.card S = (Fintype.card α)^n := by
  sorry

theorem test123 {α : Type*} [Fintype α] (n : ℕ) : False := by
  let S := {l : List α | l.length = n}
  have : Fintype S := by sorry
  have : Fintype.card S = (Fintype.card α)^n := by sorry
  sorry

lemma fsz {G: Type*} [Fintype G] [Group G] (p : ℕ) (hp : Nat.Prime p) :
  Fintype { x : List G | x.length = p ∧ x.foldl Mul.mul 1 = 1} := by
  sorry

lemma sz_x {G: Type*} [Fintype G] [Group G] (p : ℕ) (hp : Nat.Prime p) (X := { x : List G | x.length = p ∧ x.foldl Mul.mul 1 = 1}) [Fintype X] :
  Fintype.card X = (Fintype.card G)^(p-1) := by
  sorry

theorem Cauchy₁ {G: Type*} [Fintype G] [Group G] (p : ℕ) (hp : Nat.Prime p) (pdvd : p ∣ Fintype.card G) :
  ∃ x : G, orderOf x = p := by

  let X := { x : List G | x.length = p ∧ x.foldl Mul.mul 1 = 1}

  have xl : ∀ x ∈ X, x.length = p := by
    rintro x xmem
    simp [X, Set.mem_setOf] at xmem
    simp [xmem]

  have xl_lt : ∀ x ∈ X, p - 1 < x.length := by
    rintro x xmem
    simp [X, Set.mem_setOf] at xmem
    rcases xmem with ⟨xl,xmul⟩
    rw[xl]

    cases p with
    | zero => contradiction
    | succ n => rw[add_comm, Nat.one_add_sub_one]; linarith

  let Y := { x : List G | x.length = p - 1}

  have : Finite Y := by apply List.finite_length_eq
  have : (Fintype.ofFinite Y).card = (Fintype.card G)^(p-1) := by
    sorry

  have : Fintype X := sorry

  def f : X → Y :=

  let f := fun (x : X) → (y : Y) := where
  | x =>

  have yc : Y.toFinset.card = (Fintype.card G)^(p-1) := by
    sorry

  have f_bij : Bijective f := sorry
  #check f
  have : Finite X := by
    apply Function.Bijective.finite_iff.mp f_bij

  have : X.toFinset.card = Y.toFinset.card := by
    --apply Finset.card_bij
    sorry

  --have pg : p > 1 := by sorry

  -- For proving x[p-1] exists: https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.E2.9C.94.20Having.20trouble.20reasoning.20about.20list.20elements
  have : ∀ x, (hx : x ∈ X) → (x[p-1]'(xl_lt _ hx))⁻¹ = x.dropLast.foldl Mul.mul 1 := by
    rintro x xmem
    simp [X, Set.mem_setOf] at xmem
    rcases xmem with ⟨xl,xmul⟩
    apply last_elem_eq_inv_of_prod
    assumption
    assumption
    constructor <;>
    assumption
