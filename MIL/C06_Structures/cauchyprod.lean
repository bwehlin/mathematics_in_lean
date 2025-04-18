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


lemma fold_split {G: Type*} [Group G] (l : List G) (p : ℕ)  (hp : p > 1) (h : l.length = p) (f : G → G → G) :
  List.foldl f 1 (List.drop 1 l ++ List.take 1 l) = f (List.foldl f 1 (List.drop 1 l)) (List.foldl f 1 (List.take 1 l)) := by

  let l₁ := List.drop 1 l ++ List.take 1 l

  have : l ≠ [] := sorry

  have : l[0] = l.head this := by simp

  have : 0 < l.length := sorry
  have : [l[0]] = l.take 1 := by simp


  simp

lemma prod_split {G: Type*} [Group G] (l₁ l₂ : List G) (p : ℕ)  (hp : p > 1) (h : l.length = p) (f : G → G → G) :
  (l₁ ++ l₂).prod = l₁.prod * l₂.prod := by
  simp


lemma fold_split {G: Type*} [Group G] (l₁ l₂ : List G) (p : ℕ)  (hp : p > 1) (h : l.length = p) (f : G → G → G) :
  List.foldl f 1 (l₁ ++ l₂) = f (List.foldl f 1 l₁) (List.foldl f 1 l₂) := by

  let l := l₁ ++ l₂


  simp


lemma fold_list' {G: Type*} [Group G] (l : List G) (p : ℕ)  (hp : p > 1) (h : l.length = p) (f : G → G → G) :
  List.foldl f 1 (List.drop 1 l ++ List.take 1 l) = List.foldl f 1 (List.drop 1 l) * List.foldl f 1 (List.take 1 l) := by

  have : List.drop 1 l = l.tail := by simp
  rw[this]
  have : l ≠ [] := sorry
  have : List.take 1 l = [l.head this] := by
    sorry
  simp
  rw[←  List.prod]

lemma last_elem_eq_inv_of_prod {G: Type*} [Fintype G] [Group G] (p : ℕ) (hp : Nat.Prime p) (l : List G) (hl : l.length = p):
  l.length = p ∧ l.prod = 1 → (l[p-1]'(by simp[hl]; linarith[Nat.Prime.one_lt hp]))⁻¹ = l.dropLast.prod := by

  rintro ⟨_, h⟩

  have pg : p > 1 := Nat.Prime.one_lt hp
  have hl₁ : p - 1 < l.length := by
    simp[hl]
    linarith[Nat.Prime.one_lt hp]

  have xmu : (l.dropLast.prod) * (l[p-1]'hl₁) = 1 := by
    rw [List.prod_eq_foldl]
    rw [fold_list l p pg hl (fun x1 x2 ↦ x1 * x2)]
    rw [← List.prod_eq_foldl]
    exact h

  rw [← one_mul (l[p-1]'hl₁)⁻¹]
  symm
  rw [ ← div_eq_iff_eq_mul, div_eq_mul_inv, inv_inv]
  exact xmu

variable (G : Type*) [Group G] [Fintype G]
variable (p : ℕ) (h: Nat.Prime p)
def X : Set (List G) := { x : List G | x.length = p ∧ x.prod = 1}
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

    have last_x : lx[p-1] = (lx.dropLast.prod)⁻¹ := by
      apply inv_inj.mp
      rw [inv_inv]
      apply last_elem_eq_inv_of_prod
      apply hp
      exact x.2.1
      exact x.2

    have last_y : ly[p-1] = (ly.dropLast.prod)⁻¹ := by
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
  let last := (lx.prod)⁻¹
  let a := lx ++ [last]

  have : a ∈ X G p := by
    constructor
    · have : lx.length = p-1 := by apply x.2
      simp[this,a]
      exact Nat.sub_add_cancel (Nat.Prime.pos hp)
    · simp[a, last]

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

lemma comm_e {a b : G} : a * b = 1 ↔ b * a = 1 := by
  constructor
  · intro h
    apply mul_eq_one_iff_eq_inv.mp at h
    rw[h, mul_inv_cancel]
  · intro h
    apply mul_eq_one_iff_eq_inv.mp at h
    rw[h, mul_inv_cancel]

lemma action_by_generator (x : X G p) (hp : Nat.Prime p) : List.rotate x 1 ∈ (X G p) := by
  let xl := x.1
  #check x.2.1
  constructor
  · simp [X]
    apply x.2.1

  simp[X, xl]
  rw [List.rotate_eq_drop_append_take]
  #check xl.take 1
  #check x.2.1
  have : 2 ≤  x.1.length := by simp[x.2.1]; apply Nat.Prime.two_le hp
  have : 0 < x.1.length := by linarith
  have : xl ≠ [] := by sorry
  have : xl.take 1 = [xl.head this] := by
    dsimp

  have : xl.take 1 = [xl[0]] := by
    rw [List.head_eq_getElem_zero]

  --rw [← List.append_eq_has_append]

  rw [comm_e]

instance : MulAction (ZMod p) (X G p) where
  smul n x := ⟨ x.1.rotate n.val, by
    simp[X]
    constructor
    apply x.2.1
    #check x.1
    simp only [x.1] ⟩
  one_smul := by
    intro x

  mul_smul := sorry

instance (hp : Nat.Prime p) : AddAction (ZMod p) (X G p) where

  vadd n x := ⟨x.1.rotate n.val, by
    simp[X]
    constructor
    apply x.2.1
    induction' n.val with n hn
    rw[List.rotate_zero]
    apply x.2.2
    rw [← List.rotate_rotate]
    have : x.1.rotate n ∈ (X G p) := by
      constructor
      rw [List.length_rotate]
      apply x.2.1
      exact hn
    have : (x.1.rotate n).rotate 1 ∈ (X G p) := by
      apply action_by_generator G p ⟨x.1.rotate n, this⟩
      apply hp
    apply this.2
  ⟩
  add_vadd m n x := by
    sorry
  zero_vadd := sorry

theorem Cauchy₂ (hp : Nat.Prime p) (pdvd : p ∣ Fintype.card G) :
  ∃ x : G, orderOf x = p := by
  sorry
