import Mathlib

open scoped Interval
open Complex MeasureTheory

namespace Work.Idx

set_option linter.unusedVariables false in
/-- The circle integral of a constant vanishes (`z ↦ z • a` is a primitive of the constant
function `a` on the circle).

Route.  `circleIntegral.integral_eq_zero_of_hasDerivWithinAt` applied to the primitive
`z ↦ z • a` with derivative `a` (`(hasDerivAt_id z).smul_const a`), on `Metric.sphere c R`. -/
theorem circleIntegral_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (a : E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), a) = 0 := by
  have h : ∀ _z ∈ Metric.sphere c |R|,
      HasDerivWithinAt (fun z : ℂ => z • a) a (Metric.sphere c |R|) _z := fun z _ =>
    by simpa using ((hasDerivAt_id z).smul_const a).hasDerivWithinAt
  exact circleIntegral.integral_eq_zero_of_hasDerivWithinAt' h

end Work.Idx
