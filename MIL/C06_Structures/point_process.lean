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
        intro s₁ s₂ hsub
        have : ∀ x ∈ xs, (s₁.indicator fun _ ↦ 1) x ≤ (s₂.indicator fun _ ↦ 1) x := by
            intro x xmem


    iUnion_nat := by
        simp
    m_iUnion := sorry
    trim_le := sorry
