import Mathlib
import Submission.ChartLogClamp
import Submission.DirichletLim

/-!
# The piecewise barrier of the superharmonic majorant construction

This module fixes the two round functions used in the construction of a superharmonic majorant of
the clamped logarithmic potential `chartLogClamp c a ρ` on `Ω \ {x₀}` (ABS, Proposition 9).

* `Submission.chartLogPotential c a ρ A` is the (clamped) logarithmic potential
  `log ‖c x - a‖ - A` on the chart ball `chartBall c a ρ`, extended by the constant `log ρ - A`
  outside it.

* `Submission.piecewiseBarrier c a ρ s A B h₁` is the piecewise barrier: on the closed inner chart
  ball `chartClosedBall c a s` it is the logarithmic potential (the pole branch), on the remaining
  part of the chart ball it is the pointwise maximum of the logarithmic potential and the multiple
  `-B * h₁` of the Dirichlet envelope `h₁` (`Submission.limEnvelope`, with data `1` on the inner
  chart sphere and `0` on the frontier of `Ω`), and outside the chart ball it is `-B * h₁`.

Nothing of mathematical substance is asserted here; the properties of these functions (the
subharmonicity of the barrier and its pointwise comparison with the barrier `chartLogClamp`) are
proved in the companion lemmas.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The clamped logarithmic potential `log ‖c x - a‖ - A` on the chart ball `chartBall c a ρ`,
extended by the constant `log ρ - A` outside it. -/
noncomputable def chartLogPotential (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ A : ℝ) : X → ℝ :=
  fun x => if x ∈ chartBall c a ρ then Real.log ‖c x - a‖ - A else Real.log ρ - A

theorem chartLogPotential_of_mem {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ A : ℝ} {x : X}
    (hx : x ∈ chartBall c a ρ) :
    chartLogPotential c a ρ A x = Real.log ‖c x - a‖ - A := if_pos hx

theorem chartLogPotential_of_not_mem {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ A : ℝ} {x : X}
    (hx : x ∉ chartBall c a ρ) :
    chartLogPotential c a ρ A x = Real.log ρ - A := if_neg hx

/-- The piecewise barrier of the superharmonic-majorant construction. -/
noncomputable def piecewiseBarrier (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ s A B : ℝ)
    (h₁ : X → ℝ) : X → ℝ :=
  fun x =>
    if x ∈ chartClosedBall c a s then chartLogPotential c a ρ A x
    else if x ∈ chartBall c a ρ then max (chartLogPotential c a ρ A x) (-B * h₁ x)
    else -B * h₁ x

theorem piecewiseBarrier_of_mem_inner {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ s A B : ℝ}
    {h₁ : X → ℝ} {x : X} (hx : x ∈ chartClosedBall c a s) :
    piecewiseBarrier c a ρ s A B h₁ x = chartLogPotential c a ρ A x := if_pos hx

theorem piecewiseBarrier_of_mem_middle {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ s A B : ℝ}
    {h₁ : X → ℝ} {x : X} (hx : x ∉ chartClosedBall c a s) (hx' : x ∈ chartBall c a ρ) :
    piecewiseBarrier c a ρ s A B h₁ x = max (chartLogPotential c a ρ A x) (-B * h₁ x) := by
  rw [piecewiseBarrier, if_neg hx, if_pos hx']

end Submission
