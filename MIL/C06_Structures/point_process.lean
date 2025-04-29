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

--noncomputable def PointMeasure {ι : Type*} [Countable ι] (f : ι → Measure α) := Measure.sum f

example asdf := by
    let f : ℕ → α := sorry
    #check PointMeasure f
    #check PointMeasure f (Set.singleton a)
    #check Measure.dirac a (Set.singleton a)



def IsSimplePointMeasure (f : ℕ → Measure α) : Prop :=
    --∀ x : α, Measure.dirac (Set.singleton x) = 0
    ∀ x : α, PointMeasure f (Set.singleton x) = 0


class IsPointMeasure (μ : Measure α) : Prop where
    is_countable_sum {ι : Type*} [Countable ι] (f : ι → Measure α) : μ = PointMeasure f

class IsSimplePointMeasure (μ : Measure α) [IsPointMeasure μ] : Prop where
    unit_mass :
