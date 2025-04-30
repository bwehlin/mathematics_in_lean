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
    ∀ x : α, PointMeasure f {x} = 0 ∨ PointMeasure f {x} = 1

theorem dirac_of_singleton_eq_zero_or_one {a x : α} (hm : MeasurableSet {x}) :
    Measure.dirac a {x} = (0 : ENNReal) ∨ Measure.dirac a {x} = (1 : ENNReal) := by
    rw [Measure.dirac_apply' a hm]
    exact indicator_eq_zero_or_self {x} 1 a

theorem dirac_on_singleton_of_singleton_eq_one {x : α} (hm : MeasurableSet {x}) :
    Measure.dirac x {x} = (1 : ENNReal) := by
    rw [Measure.dirac_apply' x hm]
    exact (indicator_eq_one_iff_mem ENNReal).mpr rfl

theorem dirac_on_singleton_iff {a x : α} (hm : MeasurableSet {x}) :
    Measure.dirac a {x} = (1 : ENNReal) ↔ a = x := by
    constructor
    ·   intro h
        rwa [Measure.dirac_apply' a hm, indicator_eq_one_iff_mem] at h
    ·   intro h
        rw[h]
        apply dirac_on_singleton_of_singleton_eq_one
        apply hm

theorem dirac_of_singleton_eq_one_if_ne_zero {a x : α} (hm : MeasurableSet {x}) :
    Measure.dirac a {x} ≠ 0 → Measure.dirac a {x} = 1 := by
    intro h
    refine dirac_apply_of_mem ?_
    rw [Measure.dirac_apply' a hm] at h
    exact mem_of_indicator_ne_zero h

theorem sum_zeroes {S : Set ℕ} (f : S → ENNReal) (hf : ∀ i, f i = 0) : ∑' (i : S), f i = 0 := by
    exact ENNReal.tsum_eq_zero.mpr hf

theorem is_simple_if_injective {S : Set ℕ} {f : S → α} (hf: Injective f) (hm : ∀ x : α, MeasurableSet {x}) : IsSimplePointMeasure f := by
    intro x
    simp[PointMeasure]
    by_cases hx : x ∈ (f '' univ)
    ·
        have : ∃ i, f i = x := by
            refine SetCoe.exists.mpr ?_
            simp at hx
            exact hx
        obtain ⟨i,hi⟩ := this
        right
        rw [MeasureTheory.Measure.sum_apply, ENNReal.tsum_eq_add_tsum_ite i, ENNReal.tsum_eq_zero.mpr, add_zero, dirac_on_singleton_iff]
        assumption
        apply hm
        intro j
        by_cases hj: j = i
        simp[hj]
        simp[hj]
        have : f j ≠ f i := by
            push_neg at hj
            contrapose! hj
            apply hf
            exact hj
        contrapose! this
        rw[hi]
        apply dirac_of_singleton_eq_one_if_ne_zero at this
        rw [dirac_on_singleton_iff] at this
        exact this
        repeat apply hm

    ·
        left
        have : ∀ (i : S), dirac (f i) {x} = 0 := by
            intro i
            contrapose! hx
            apply dirac_of_singleton_eq_one_if_ne_zero at hx
            rw [dirac_on_singleton_iff] at hx
            refine (mem_image f univ x).mpr ?_
            use i
            simp
            exact hx
            apply hm
            apply hm
        intro a as
        specialize this ⟨a, as⟩
        exact this
