import Mathlib.Tactic
import Mathlib.Util.Delaborators

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac

import Mathlib.Algebra.Group.Indicator

set_option warningAsError false

noncomputable section

open MeasureTheory

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α} {a : α}

-- sample space α

--def RandomMeasure : α → β :=

noncomputable def PointMeasure₁ (xs : List α) : Measure α where
    measureOf s := (xs.map (fun x ↦ Measure.dirac x)).sum s
    empty := by simp
    mono := by exact fun {s₁ s₂} a ↦ OuterMeasureClass.measure_mono (List.map (fun x ↦ Measure.dirac x) xs).sum a
    iUnion_nat := by exact fun s a ↦ OuterMeasureClass.measure_iUnion_nat_le (List.map (fun x ↦ Measure.dirac x) xs).sum s a

    m_iUnion := by

        intro f hm hpwd
        apply OuterMeasure.iUnion_nat
        apply OuterMeasure.iUnion_eq_of_caratheodory
        intro i
        specialize hm i

        refine fun i ↦ ?_
        specialize hm i


        refine
          OuterMeasure.iUnion_eq_of_caratheodory
            { measureOf := fun s ↦ (List.map (fun x ↦ Measure.dirac x) xs).sum s,
              empty := of_eq_true (Eq.trans (congrArg (fun x ↦ x = 0) measure_empty) (eq_self 0)),
              mono := fun {s₁ s₂} a ↦
                OuterMeasureClass.measure_mono (List.map (fun x ↦ Measure.dirac x) xs).sum a,
              iUnion_nat := fun s a ↦
                OuterMeasureClass.measure_iUnion_nat_le (List.map (fun x ↦ Measure.dirac x) xs).sum
                  s a }
            ?_ hpwd
        intro i
        specialize hm i




def PointMeasure (xs : List α) : Measure α where
    measureOf s := (xs.map (s.indicator fun _ ↦ 1)).sum
    empty := by simp
    mono := by
        intro _ _ hsub
        refine List.sum_le_sum ?_
        intro _ _
        refine Set.indicator_le_indicator_apply_of_subset hsub ?_
        exact zero_le_one' ENNReal

    iUnion_nat := by
        intro f hpwd
        simp

        have : ∀ x : α, (⋃ i, f i).indicator (fun _ ↦ 1) x = ∑' (i : ℕ), (f i).indicator (fun _ ↦ 1) x := by
            intro x
            have hij : ∀ (i j : ℕ) (h : i ≠ j), Disjoint (f i) (f j) := by
                rintro i j h
                apply hpwd h

            have hu : ⋃ i, f i = f 0 ∪ (⋃ (j : ℕ), f (j+1)) := by
                exact Eq.symm (Set.union_iUnion_nat_succ f)

            have : Disjoint (f 0) (⋃ i, f (i+1)) := by
                refine Set.disjoint_iUnion_right.mpr ?_
                intro i
                specialize hij 0 (i+1)
                have : 0 ≠ i + 1 := by simp
                exact hpwd this

            have : (⋃ i, f i).indicator (fun _ ↦ 1) x = (f 0).indicator (fun _ ↦ 1) x + (⋃ i, f (i+1)).indicator (fun _ ↦ 1) x := by
                rw[hu, Set.indicator_union_of_disjoint this]

            sorry
        apply Set.indicator_union_of_disjoint
        simp

    m_iUnion := sorry
    trim_le := sorry
