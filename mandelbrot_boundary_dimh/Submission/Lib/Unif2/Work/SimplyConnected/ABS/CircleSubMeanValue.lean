import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg

/-!
# Circle sub-mean-value and super-mean-value inequalities without continuity

The library definition `Submission.SubharmonicAtChart u c x` (Hubbard's Definition 1.2.1) asks
for a *continuous* function satisfying the circle mean-value inequality.  For the barrier
comparison needed in `Work.SimplyConnected.ABS.limEnvelope_lt_near_of_barrier` one must work
with functions that are only *upper* (respectively *lower*) semicontinuous: the clamped barrier
`x ↦ if x ∈ V then min (h x) C else C` is upper semicontinuous, but it jumps down at `∂V` in
general.

This module provides the two continuity-free notions.

* `Work.SimplyConnected.ABS.CircleSubMeanValueAtX w x` — the circle sub-mean-value inequality
  `w p ≤ ⨍ w` on every sufficiently small circle centred near `x`, in the chart at `x`.
* `Work.SimplyConnected.ABS.CircleSuperMeanValueAtX w x` — the reverse inequality.

Nothing of mathematical substance lives here; the lemmas about these notions are stated in the
consuming modules.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Circle sub-mean-value inequality at `x`, without continuity.**  There is a ball around
`c x` in the chart `c = chartAt ℂ x` (the preferred chart) on which the pullback
`w ∘ c.symm` satisfies `w p ≤ ⨍ w` on every circle centred at `p` and contained in that ball. -/
def CircleSubMeanValueAtX (w : X → ℝ) (x : X) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
    ∀ p ∈ Metric.ball ((chartAt ℂ x) x) ρ, ∀ r : ℝ, 0 < r →
      Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ x) x) ρ →
      (w ∘ (chartAt ℂ x).symm) p ≤ Real.circleAverage (w ∘ (chartAt ℂ x).symm) p r

/-- **Circle super-mean-value inequality at `x`, without continuity.** -/
def CircleSuperMeanValueAtX (w : X → ℝ) (x : X) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
    ∀ p ∈ Metric.ball ((chartAt ℂ x) x) ρ, ∀ r : ℝ, 0 < r →
      Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ x) x) ρ →
      Real.circleAverage (w ∘ (chartAt ℂ x).symm) p r ≤ (w ∘ (chartAt ℂ x).symm) p

end Work.SimplyConnected.ABS
