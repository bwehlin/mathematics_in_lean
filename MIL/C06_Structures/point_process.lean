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

noncomputable def PointMeasure (f : ℕ → α) : Measure α := Measure.sum (fun i ↦ Measure.dirac (f i))

def IsSimplePointMeasure (f : ℕ → α) : Prop :=
    ∀ x : α, PointMeasure f (Set.singleton x) = 0 ∨ PointMeasure f (Set.singleton x) = 1
