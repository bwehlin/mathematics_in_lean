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

        simp

    m_iUnion := sorry
    trim_le := sorry
