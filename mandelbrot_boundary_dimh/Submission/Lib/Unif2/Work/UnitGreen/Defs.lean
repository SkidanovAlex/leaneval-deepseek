import Mathlib
import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.Holomorphic
import Submission.Lib.Unif2.GreenData
import Submission.Lib.Unif2.Work.Parabolic.Basic

/-!
# Unit-pole Green functions

`Work.Parabolic.IsGreenFunctionAt z₀ E` (the corrected, satisfiable notion of a Green function)
does **not** normalise the coefficient of the logarithmic pole at `z₀`.  The holomorphic-modulus
statement `‖Φ x‖ = exp (-E x)` with `Φ` holomorphic and `HasLogPoleAt z₀ Φ` (a *simple* zero)
forces that coefficient to be exactly one, so it must be assumed:

`IsUnitGreenFunctionAt z₀ E` = `IsGreenFunctionAt z₀ E` together with
`|E x + log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖| ≤ C` on a punctured neighbourhood of `z₀`.

Rescaling a Green function `E` with pole coefficient `c > 0` to `E / c` produces a unit-pole one
(and `c > 0` is forced by positivity plus the maximum principle), so nothing is lost.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff

noncomputable section

open Filter Set

namespace Work.UnitGreen

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **A Green function whose logarithmic pole has coefficient exactly one.** -/
def IsUnitGreenFunctionAt (z₀ : X) (E : X → ℝ) : Prop :=
  Work.Parabolic.IsGreenFunctionAt (X := X) z₀ E ∧
  ∃ C : ℝ, ∃ V : Set X, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ →
    |E x + Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖| ≤ C

/-- A unit-pole Green function is a Green function. -/
theorem IsUnitGreenFunctionAt.isGreenFunctionAt {z₀ : X} {E : X → ℝ}
    (h : IsUnitGreenFunctionAt z₀ E) : Work.Parabolic.IsGreenFunctionAt (X := X) z₀ E := h.1

end Work.UnitGreen
