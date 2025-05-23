import MIL.Common
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Init.Data.Vector.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.PGroup

noncomputable section

-- This proof is based chiefly on `Proof 2` on Wikipedia (`https://en.wikipedia.org/wiki/Cauchy%27s_theorem_(group_theory)` 2025-04-29)
-- However, we use a different approach towards the end where instead of "counting the elements of X by orbits...",
-- we use a congruence lemma (see further down).

-- Note: I have used leansearch.net extensively to figure out theorem names etc.
-- Since this maybe counts as using AI, I wanted to at least disclose it. `apply?`
-- has also been very helpful, except in `theorem Cauchy₂` where Lean simply
-- suggests to use the Mathlib proof :)

set_option linter.unusedSectionVars false

open Group
open Function
open Set

variable (G : Type*) [Group G] [Fintype G]
variable (p : ℕ) [hp : Fact p.Prime]
def X : Set (List G) := { x : List G | x.length = p ∧ x.prod = 1}
def Y : Set (List G) := { x : List G | x.length = p - 1}

-- First goal is to establish that X and Y have the same cardinality.
-- The cardinality of Y is easily seen to be G^(p-1).

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

-- Thanks to Hampus Nyberg for helping with untangling the (X G p) syntax and
-- pulling out the pieces (x.2.1, etc.)
def f : X G p → Y G p := fun x => ⟨ x.val.dropLast, by simp[Y]; rw [x.property.1] ⟩

lemma f_inj  : Injective (f G p)  := by
  rintro x y h
  simp [f] at h

  let lx := x.1
  let ly := y.1

  have : x.1 = y.1 := by
    have hx1 := x.2.1
    have hx2 := x.2.2

    have hy1 := y.2.1
    have hy2 := y.2.2

    have : p-1 < lx.length := by
      simp[lx, x.2.1]
      exact Nat.Prime.pos hp.out

    have : p-1 < ly.length := by
      simp[ly, y.2.1]
      exact Nat.Prime.pos hp.out

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
      apply hp.out
      exact x.2.1
      exact x.2

    have last_y : ly[p-1] = (ly.dropLast.prod)⁻¹ := by
      apply inv_inj.mp
      rw [inv_inv]
      apply last_elem_eq_inv_of_prod
      apply hp.out
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

lemma f_surj : Surjective (f G p)  := by
  intro x
  let lx := x.1
  let last := (lx.prod)⁻¹
  let a := lx ++ [last]

  have : a ∈ X G p := by
    constructor
    · have : lx.length = p-1 := by apply x.2
      simp[this,a]
      exact Nat.sub_add_cancel (Nat.Prime.pos hp.out)
    · simp[a, last]

  refine SetCoe.exists.mpr ?_
  use a
  constructor
  simp[f,a]
  rfl
  exact this

lemma f_bij : Bijective (f G p) := by
  constructor
  apply f_inj
  apply f_surj

lemma xy_card : Nat.card (X G p) = Nat.card (Y G p) := by
  apply Nat.card_eq_of_bijective (f G p)
  apply f_bij

lemma Y_finite : Finite (Y G p) := by
  apply List.finite_length_eq

instance : Fintype (Y G p) := by
  have : Finite (Y G p) := by apply List.finite_length_eq
  apply Fintype.ofFinite (Y G p)

lemma card_y : Fintype.card (Y G p) = (Fintype.card G)^(p-1) := by
  have : Y G p = List.Vector G (p-1) := by simp[Y, List.Vector]
  simp[this]

lemma card_x : Nat.card (X G p) = (Fintype.card G)^(p-1) := by
  rw [← card_y,  Fintype.card_eq_nat_card, xy_card]

lemma X_finite : Finite (X G p) := by
  have : Nat.card (X G p) = (Fintype.card G)^(p-1) := by apply card_x
  have : Nat.card (X G p) ≠ 0 := by simp[this]
  apply Nat.finite_of_card_ne_zero this

lemma p_div_gp (pdiv : p ∣ Fintype.card G) : p ∣ (Fintype.card G)^(p-1) := by
  rcases pdiv with ⟨n,hn⟩
  rw[hn]
  refine Dvd.dvd.pow ?_ ?_
  simp
  have : p -  1 = p.totient := by
    refine Eq.symm (Nat.totient_prime ?_)
    apply hp.out
  rw[this]
  exact Ne.symm (NeZero.ne' p.totient)

-- Next, we will define an action of (ZMod p) on (X G p) by n +ᵥ x = x.rotate n.val,
-- i.e., a leftwards rotation by n. We do this by definining the action by the generator,
-- 1, and then inductively for n.

lemma comm_e {a b : G} : a * b = 1 ↔ b * a = 1 := by
  constructor
  · intro h
    apply mul_eq_one_iff_eq_inv.mp at h
    rw[h, mul_inv_cancel]
  · intro h
    apply mul_eq_one_iff_eq_inv.mp at h
    rw[h, mul_inv_cancel]

lemma action_by_generator (x : X G p) (hp : Nat.Prime p) : List.rotate x 1 ∈ (X G p) := by

  constructor
  · simp
    apply x.2.1

  let xl := x.1

  have nonempty : x.1 ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    rw[x.2.1]
    apply Nat.Prime.pos hp

  have zero_lt : 0 < x.1.length := by
    refine List.length_pos.mpr ?_
    apply nonempty

  let b := xl.tail.prod
  let a := xl[0]

  have a_eq_a_prod : a = [a].prod := by simp

  have singleton_append_eq_cons (l : List G) : ∀ x : G, [x] ++ l = x :: l := by simp

  have : a * b = 1 := by
    rw [a_eq_a_prod]
    rw [← List.prod_append]
    simp only[a]
    rw [← List.head_eq_getElem_zero nonempty]
    rw [singleton_append_eq_cons]
    rw [List.head_cons_tail]
    apply x.2.2

  have b_a_eq_one : b * a = 1 := by
    rw [comm_e]
    apply this

  have : xl.head nonempty = xl[0] := by
    exact List.head_eq_getElem xl nonempty

  have : xl.head? = xl[0] := by
    exact (List.head_eq_iff_head?_eq_some nonempty).mp this

  have : xl.rotate 1 = xl.tail ++ [xl[0]] := by
    rw [List.rotate_eq_drop_append_take]
    simp
    rw [List.take_one]
    rw[this]
    simp
    linarith

  rw[this, List.prod_append, ← a_eq_a_prod, b_a_eq_one]

instance zmod_action : AddAction (ZMod p) (X G p) where

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
      apply hp.out
    apply this.2
  ⟩

  add_vadd m n x := by
    simp [· +ᵥ ·] -- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.E2.9C.94.20How.20to.20expand.20definition.20within.20instance.3F/with/513063729
    have : NeZero p := ⟨ Nat.Prime.ne_zero hp.out ⟩
    rw [List.rotate_rotate, ZMod.val_add]
    have : p = x.1.length := by symm; apply x.2.1
    simp[this]
    rw[List.rotate_mod, add_comm]

  zero_vadd x := by simp [· +ᵥ ·]

instance : AddGroup (ZMod p) where
  neg_add_cancel := by simp

instance : Group (Multiplicative (ZMod p)) where
  inv_mul_cancel := by simp

-- Showing that (ZMod p) is a p-group lets us argue about the fixed points of the
-- action on (X G p). Mathlib only has PGroups for MulActions, so we will turn
-- the additive structure on (ZMod p) into the corresponding multiplicative
-- structure using Multiplicative.

lemma zmodp_mul_is_pgroup : IsPGroup p (Multiplicative (ZMod p)) := by
  apply IsPGroup.iff_card.mpr
  use 1
  simp

-- The key result here is that |X| ≡ |{fixed points of the action}| mod p.
-- (Thanks Kim Kiehn for pointing this out!). Because p is prime, we can arrive
-- at a slightly stronger lemma:

lemma card_fixed (pdvd : p ∣ Fintype.card G) : p ∣ Nat.card ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) := by

  have : ∃ (k : ℕ), (Fintype.card G)^(p-1) = k * p := by
    have : p ∣ (Fintype.card G)^(p-1) := by
      apply p_div_gp
      apply pdvd
    rcases this with ⟨l,hl⟩
    use l
    rwa[mul_comm]

  have zero_mod : (Fintype.card G)^(p-1) ≡ 0 [MOD p] := by
    refine Nat.modEq_zero_iff_dvd.mpr ?_
    apply p_div_gp
    apply pdvd

  have : (Fintype.card G)^(p-1) ≡ Nat.card ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) [MOD p] := by
    have : Nat.card (X G p) ≡ Nat.card ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) [MOD p] := by
      have : Finite (X G p) := by apply X_finite
      apply IsPGroup.card_modEq_card_fixedPoints
      apply zmodp_mul_is_pgroup
    rwa [card_x] at this

  have : Nat.card ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) ≡ 0 [MOD p] := by
    exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm zero_mod)) this)

  exact Nat.dvd_of_mod_eq_zero this


-- Since (1,...,1) ∈ fixedPoints, we have |fixedPoints| ≠ ∅

lemma card_pos : Nonempty ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) := by

  refine nonempty_iff_ne_empty'.mpr ?_

  let ones : (X G p) := ⟨List.replicate p 1, by simp[X]⟩
  have ident_ones : ∀ n : ℕ, ones.1.rotate n = ones.1 := by
    exact fun n ↦ List.rotate_replicate 1 p n

  have : ones ∈ (MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) := by
    refine MulAction.mem_fixedPoints.mpr ?_
    intro m
    have : ∀ n : (ZMod p), n +ᵥ ones = ones := by
      intro n
      simp [· +ᵥ ·, zmod_action, ident_ones]
    exact this (Multiplicative.toAdd m)

  exact ne_of_mem_of_not_mem' this fun a ↦ a

-- Now, using that p is prime, we see that |fixedPoints| > 1, meaning that there
-- is at least one x ∈ (X G p) that is not equal to (1,...,1).

lemma card_gt (pdvd : p ∣ Fintype.card G) : Nat.card ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) > 1 := by
  have pdivc : p ∣ Nat.card ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) := by
    apply card_fixed;
    apply pdvd
  have : Nonempty ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) := by
    apply card_pos

  have : Finite (X G p) := by apply X_finite
  have : Finite ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) := by
    exact Subtype.finite

  have : Nat.card ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) > 0 := by
    simp

  have : ∃ (n : ℕ), Nat.card ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) = n * p := by
    exact exists_eq_mul_left_of_dvd pdivc

  rcases this with ⟨n, hn⟩
  have ngt : n > 0 := by
    rw [hn] at this
    exact Nat.pos_of_mul_pos_right this

  have : n * p > 0 := by
    exact Nat.lt_of_lt_of_eq this hn
  have : p > 1 := by
    apply Nat.Prime.one_lt hp.out
  have : n * p > 1 := by
    exact Right.one_lt_mul_of_le_of_lt ngt this

  linarith

-- Next, let's prove that x ∈ fixedPoints ↔ x = (a,...,a) for some (a : G).

-- For how to deal with the hypothesis `ha`: https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Existence.20with.20'and'.20where.20one.20of.20the.20terms.20needs.20the.20other/with/514218988
lemma fixed_constant (x : (X G p)) : x ∈ ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) ↔ (∃ a : G, ∃ (ha: a^p=1), x = ⟨List.replicate p a, by simp[X]; apply ha⟩) := by
  constructor
  rintro hx

  have act : ∀ (n : Multiplicative (ZMod p)), n • x = x := by
    intro n
    exact hx n

  have : ∀ (m : ℕ), x.1.rotate m ∈ (X G p) := by
    intro m
    simp[X]
    constructor
    apply x.2.1
    refine List.prod_rotate_eq_one_of_prod_eq_one ?_ m
    apply x.2.2


  have : ∀ (n : Multiplicative (ZMod p)), n • x = ⟨ x.1.rotate n.val,by apply this⟩  := by
    intro n
    exact rfl

  have : ∀ (n : ℕ), x.1.rotate n = x.1 := by
    intro n
    let m : ZMod p := n
    specialize act m
    specialize this m
    rw[act] at this
    symm
    rw[ZMod.val_natCast] at this

    have : x.1 = x.1.rotate (n % p) := by
      nth_rw 1 [this]

    have peq : p = x.1.length := by
      symm
      apply x.2.1

    simp[peq] at this
    rw[List.rotate_mod] at this
    exact this

  apply List.rotate_eq_self_iff_eq_replicate.mp at this
  rcases this with ⟨a, ha⟩

  have : a^p = 1 := by
    by_contra h
    push_neg at h
    have : x.1.prod = a^p := by
      rw[ha]
      rw [List.prod_replicate]
      simp[x.2.1]
    have : x.1.prod ≠ 1 := by
      rw[this]
      exact h
    have : x.1.prod = 1 := by
      simp[x.2.2]
    contradiction

  use a
  simp[this]
  refine SetCoe.ext ?_
  have : p = x.1.length := by symm; apply x.2.1
  simp[this]
  exact ha


  -- <-

  rintro ⟨a, ha⟩ n
  rcases ha with ⟨ha, hx⟩

  have xin : x.1.rotate n.val ∈ X G p := by
    simp[X]
    constructor
    apply x.2.1
    refine List.prod_rotate_eq_one_of_prod_eq_one ?_ (ZMod.val n)
    apply x.2.2

  let m : ZMod p := n

  have : n • x = m +ᵥ x := by
    exact rfl

  have : n • x = ⟨ x.1.rotate n.val, by apply xin⟩ := by
    exact this

  rw[this]
  simp[hx]

-- x = (a,...,a) ∧ x = (b,...,b) ↔ a ≠ b
lemma list_repl (a b : G) (x : List G) (hx : x = List.replicate p a) (hb : x ≠ List.replicate p b) : a ≠ b := by
  contrapose! hb
  have : List.replicate p a = List.replicate p b ↔ a = b := by
    apply List.replicate_right_inj
    apply Nat.Prime.ne_zero hp.out
  rw[← this] at hb
  rwa [hb] at hx

-- We are now ready to prove the theorem! Remember that p is assumed to be prime
-- in the section-wide hypothesis [hp : Fact p.Prime]
theorem Cauchy₂ (pdvd : p ∣ Fintype.card G) :
  ∃ x : G, orderOf x = p := by

  have cpos : Nat.card ↑(MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) > 1 := by
    exact card_gt G p pdvd

  let ones : (X G p) := ⟨List.replicate p 1, by simp[X]⟩

  have ident_ones : ∀ n : ℕ, ones.1.rotate n = ones.1 := by
    exact fun n ↦ List.rotate_replicate 1 p n

  -- We establish that ones:=(1,...,1) ∈ fixedPoints and that there is some
  -- x:=(a,...,a) ∈ fixedPoints but that x ≠ ones

  have : ones ∈ (MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)) := by
    simp[X, · +ᵥ ·, zmod_action]
    intro n
    simp [ident_ones]

  have : ∃ x ∈ (MulAction.fixedPoints (Multiplicative (ZMod p)) (X G p)), x ≠ ones := by
    exact exists_ne_of_one_lt_ncard cpos ones

  rcases this with ⟨x, hx, x_ne_ones⟩
  rw [fixed_constant] at hx
  rcases hx with ⟨g, hgp, hgr⟩

  use g
  refine orderOf_eq_prime hgp ?_ -- for prime order it is enough to show that g ≠ 1

  simp only [ones] at x_ne_ones
  refine Ne.symm (list_repl G p 1 g (List.replicate p 1) ?_ ?_)
  rw[hgr] at x_ne_ones
  symm
  rw[hgr] at x_ne_ones
  simp at x_ne_ones
  simp
  exact x_ne_ones
