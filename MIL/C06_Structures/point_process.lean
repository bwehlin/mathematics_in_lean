import Mathlib.Tactic
import Mathlib.Util.Delaborators

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac

import Mathlib.Algebra.Group.Indicator

set_option warningAsError false

noncomputable section

open MeasureTheory
open MeasureTheory.Measure
open Function
open Set

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α} {a : α}

-- sample space α

--def RandomMeasure : α → β :=

noncomputable def PointMeasure {S : Set ℕ} (f : S → α) : Measure α := Measure.sum (fun i ↦ Measure.dirac (f i))

def IsSimplePointMeasure {S : Set ℕ} (f : S → α)  : Prop :=
    ∀ x : α, PointMeasure f (Set.singleton x) = 0 ∨ PointMeasure f (Set.singleton x) = 1

theorem dirac_of_singleton_eq_zero_or_one {a x : α} (hm : MeasurableSet (Set.singleton x)) :
    Measure.dirac a (Set.singleton x) = (0 : ENNReal) ∨ Measure.dirac a (Set.singleton x) = (1 : ENNReal) := by
    rw [Measure.dirac_apply' a hm]
    exact indicator_eq_zero_or_self (Set.singleton x) 1 a

theorem dirac_of_singleton_eq_one_if_ne_zero {a x : α} (hm : MeasurableSet (Set.singleton x)) :
    Measure.dirac a (Set.singleton x) ≠ 0 → Measure.dirac a (Set.singleton x) = 1 := by
    intro h
    refine dirac_apply_of_mem ?_
    rw [Measure.dirac_apply' a hm] at h
    exact mem_of_indicator_ne_zero h

theorem asdf {S : Set ℕ} {f : S → ℕ} : False := by
    #check f
    let y := f '' univ

    sorry

theorem is_simple_if_injective {S : Set ℕ} {f : S → α} (hf: Injective f) (hm : ∀ x : α, MeasurableSet (Set.singleton x)) : IsSimplePointMeasure f := by
    intro x

    let xf := f⁻¹' (Set.singleton x)
    have : Set.Subsingleton xf := by
        apply Set.Subsingleton.preimage
        exact Set.subsingleton_of_subset_singleton fun ⦃a⦄ ↦ congrArg fun ⦃a⦄ ↦ a
        apply hf

    #check S
    #check ↑S
    by_cases hx : x ∈ (f '' univ)

    have : ∃ i, f i = x := by
        refine SetCoe.exists.mpr ?_
        simp at hx
        exact hx

    rcases this with ⟨i, hfi⟩

    have : ∀ j, ∀ (h: f j = x), j = i := by
        rintro ⟨j, hjs⟩
        exact fun h ↦ hf (congrArg f (this h hfi))

    simp [PointMeasure]
    right

    have : dirac (f i) (Set.singleton x) = 1 := by
        rw[hfi]
        exact dirac_apply_of_mem rfl

    have : ∀ j, ∀ (h : j ≠ i), dirac (f j) (Set.singleton x) = 0 := by
        intro j
        contrapose!



    contrapose! hf

    have : PointMeasure f (Set.singleton x) ≥ 2 := by
        rcases hf with ⟨hz,ho⟩
        sorry


    refine not_injective_iff.mpr ?_
    have : ∀ i, Measure.dirac (f i) (Set.singleton x) = 0 ∨ Measure.dirac (f i) (Set.singleton x) = 1 := by
        intro i
        apply dirac_of_singleton_eq_zero_or_one
        apply hm

    simp[PointMeasure] at this
    have : ∃ i j : ℕ, ∃ (inej : i ≠ j), f i = f j := by



theorem is_simple_if_unique {f : ℕ → α} (hf : ∀ i j (hu : i ≠ j), f i ≠ f j) : IsSimplePointMeasure f := by
    intro x
    have :
