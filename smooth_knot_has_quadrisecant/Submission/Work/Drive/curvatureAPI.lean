import Mathlib
import ChallengeDeps
import Submission.TrisecantTransverse
import Submission.Commons.Analysis.Analytic.finite_zeros_of_analytic_periodic
import Submission.Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
import Submission.Commons.Analysis.CrossProduct.cross3_ne_zero_iff_linearIndependent

/-!
# API module for the "close curve with nowhere vanishing curvature" brick

Re-exports the trusted definitions (`IsSmoothKnot`, `velocity`, `period`, ...), the workspace
cross-product API (`cross3`, `cross3_ne_zero_iff_linearIndependent_local`, ...) and the analytic
finiteness-of-zeros lemma, plus the two local abbreviations used by the brick:

* `Work.Drive.accel r t = deriv (velocity r) t` — the acceleration;
* `Work.Drive.inflec r t = cross3 (velocity r t) (accel r t)` — the curvature vector, whose
  vanishing is exactly the inflection/zero-curvature condition.

Nothing mathematical is proved here.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- Acceleration of a parametrised curve: the derivative of its velocity. -/
noncomputable def accel (r : ℝ → Space) (t : ℝ) : Space := deriv (velocity r) t

/-- The curvature vector `velocity × acceleration` of a parametrised curve; it vanishes exactly at
the inflection parameters (where the curve is straight to second order). -/
noncomputable def inflec (r : ℝ → Space) (t : ℝ) : Space := cross3 (velocity r t) (accel r t)

end Work.Drive
