import MIL.Common
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Init.Data.Vector.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.BigOperators

#check Group

noncomputable section

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

variable (G : Type*) [Group G] [Fintype G]
variable (p : ℕ) (h: Nat.Prime p)
def X : Set (List G) := { x : List G | x.length = p ∧ x.foldl Mul.mul 1 = 1}
def Y : Set (List G) := { x : List G | x.length = p - 1}

def f : X G p → Y G p := fun x => ⟨ x.val.dropLast, by simp[Y]; rw [x.property.1] ⟩

#check last_elem_eq_inv_of_prod

lemma f_inj (hp: Nat.Prime p) : Injective (f G p)  := by
  rintro x y h
  simp [f] at h

  let lx := x.1
  let ly := y.1

  -- TODO: This should be refactored to avoid repetition, but it works
  have : x.1 = y.1 := by
    have hx1 := x.2.1
    have hx2 := x.2.2

    have hy1 := y.2.1
    have hy2 := y.2.2

    have : p-1 < lx.length := by
      simp[lx, x.2.1]
      exact Nat.Prime.pos hp

    have : p-1 < ly.length := by
      simp[ly, y.2.1]
      exact Nat.Prime.pos hp

    have lx_ne : lx ≠ [] := by
      apply List.length_pos_iff_ne_nil.mp
      linarith

    have ly_ne : ly ≠ [] := by
      apply List.length_pos_iff_ne_nil.mp
      linarith

    have last_x : lx[p-1] = (lx.dropLast.foldl Mul.mul 1)⁻¹ := by
      apply inv_inj.mp
      rw [inv_inv]
      apply last_elem_eq_inv_of_prod
      apply hp
      exact x.2.1
      exact x.2

    have last_y : ly[p-1] = (ly.dropLast.foldl Mul.mul 1)⁻¹ := by
      apply inv_inj.mp
      rw [inv_inv]
      apply last_elem_eq_inv_of_prod
      apply hp
      exact y.2.1
      exact y.2

    have : lx[p-1] = lx.getLast lx_ne := by
      simp[← x.2.1]
      have : lx.length - 1 < lx.length := by
        simp [hp]
        rw [x.2.1]
        linarith
      rw [←  List.get_length_sub_one this]
      simp[x.2.1, lx]

    have c_x : lx = lx.dropLast ++ [lx[p-1]] := by
      symm
      rw [this]
      rw [List.dropLast_append_getLast]

    have : ly[p-1] = ly.getLast ly_ne := by
      simp[← y.2.1]
      have : ly.length - 1 < ly.length := by
        simp [hp]
        rw [y.2.1]
        linarith
      rw [←  List.get_length_sub_one this]
      simp[y.2.1, ly]

    have c_y : ly = ly.dropLast ++ [ly[p-1]] := by
      symm
      rw [this]
      rw [List.dropLast_append_getLast]

    have : lx = ly := by
      rw [last_x] at c_x
      rw [h] at c_x
      rw [c_x]
      rw [← last_y, ← c_y]

    simp[lx, ly, this]

  exact SetCoe.ext this

lemma f_surj (hp: Nat.Prime p) : Surjective (f G p)  := by
  intro x
  let lx := x.1
  let last := (lx.foldl Mul.mul 1)⁻¹
  let a := lx ++ [last]

  have : a ∈ X G p := by
    constructor
    · have : lx.length = p-1 := by apply x.2
      simp[this,a]
      exact Nat.sub_add_cancel (Nat.Prime.pos hp)
    · simp[a, last]
      exact mul_inv_cancel (List.foldl Mul.mul 1 lx)

  refine SetCoe.exists.mpr ?_
  use a
  constructor
  simp[f,a]
  rfl
  exact this

lemma f_bij (hp : Nat.Prime p) : Bijective (f G p) := by
  constructor
  apply f_inj
  exact hp
  apply f_surj
  exact hp

lemma xy_card (hp : Nat.Prime p) : Nat.card (X G p) = Nat.card (Y G p) := by
  apply Nat.card_eq_of_bijective (f G p)
  apply f_bij
  apply hp

lemma Y_finite : Finite (Y G p) := by
  apply List.finite_length_eq

instance : Fintype (Y G p) := by
  have : Finite (Y G p) := by apply List.finite_length_eq
  apply Fintype.ofFinite (Y G p)

lemma card_y : Fintype.card (Y G p) = (Fintype.card G)^(p-1) := by
  have : Y G p = List.Vector G (p-1) := by simp[Y, List.Vector]
  simp[this]

lemma card_x (hp: Nat.Prime p) : Nat.card (X G p) = (Fintype.card G)^(p-1) := by
  rw [← card_y,  Fintype.card_eq_nat_card, xy_card]
  apply hp

lemma X_finite (hp : Nat.Prime p) : Finite (X G p) := by
  have : Nat.card (X G p) = (Fintype.card G)^(p-1) := by apply card_x; apply hp
  have : Nat.card (X G p) ≠ 0 := by simp[this]
  apply Nat.finite_of_card_ne_zero this

lemma p_div_gp (hp : Nat.Prime p) (hg : Fintype.card G = p) : p ∣ (Fintype.card G)^(p-1) := by
  rw [hg]
  apply dvd_pow_self
  have : p ≥ 2 := Nat.Prime.two_le hp
  apply Nat.one_le_iff_ne_zero.mp
  have : 0 < p := by linarith[Nat.Prime.two_le hp]
  have : p -  1 = p.totient := by
    apply Nat.totient_eq_iff_prime at this
    symm
    apply this.mpr
    apply hp
  rw[this]
  apply Nat.totient_pos.mpr
  assumption

theorem Cauchy₂ (hp : Nat.Prime p) (pdvd : p ∣ Fintype.card G) :
  ∃ x : G, orderOf x = p := by
  sorry


theorem Cauchy₁ {G: Type*} [Fintype G] [Group G] (p : ℕ) (hp : Nat.Prime p) (pdvd : p ∣ Fintype.card G) :
  ∃ x : G, orderOf x = p := by

  instance : Fintype (X G p) := by
  apply Fintype.ofFinite (X G p)

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
