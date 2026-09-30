import Mathlib
import Submission.Work.Curvature.Basic
import Submission.Work.Curvature.Deriv
import Submission.Work.Curvature.warped_sec_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Non-positivity of the sectional curvature of the warped model

The warped model metric of the filling region is
`warpedMetric f h = diag(1, f(r)², h(r)², h(r)²)`, `r = q 0`, a multiply warped
product.  Its sectional curvature numerator was computed in
`Work.Curvature.warped_sec_eq`:

`⟨R(u,v)v,u⟩ = - ( f f'' (u₀v₁-u₁v₀)² + h h'' [(u₀v₂-u₂v₀)² + (u₀v₃-u₃v₀)²]
                  + f h f' h' [(u₁v₂-u₂v₁)² + (u₁v₃-u₃v₁)²] + h² h'² (u₂v₃-u₃v₂)² )`.

Every coefficient `f f''`, `h h''`, `f h f' h'`, `h² h'²` is non-negative as soon
as `f > 0`, `h > 0`, `f' ≥ 0`, `h' ≥ 0`, `f'' ≥ 0`, `h'' ≥ 0` at `r = q 0`, so the
numerator is `≤ 0`: the filling region has non-positive sectional curvature, and
the whole warped region is non-positively curved.

This is the third of the three model inputs of the curvature chapter
(`uhs_sec`, `warped_sec_nonpos`, `flat_sec`) feeding Cartan–Hadamard.
-/

open scoped RealInnerProductSpace
open Filter Topology

namespace Work.Curvature

/-- **Non-positive sectional curvature of the warped model.**

If the warping functions satisfy `f > 0`, `h > 0` and have non-negative first and
second derivatives at `r = q 0`, then the sectional curvature numerator
`warpedMetric f h q (modelCurv (warpedMetric f h) q u v v) u = ⟨R(u,v)v,u⟩` of the
warped metric is `≤ 0` for all vectors `u`, `v`. -/
theorem warped_sec_nonpos (f h : ℝ → ℝ) (q : E4) (u v : E4)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h)
    (hf0 : 0 < f (q 0)) (hh0 : 0 < h (q 0))
    (hf1 : 0 ≤ deriv f (q 0)) (hh1 : 0 ≤ deriv h (q 0))
    (hf2 : 0 ≤ deriv^[2] f (q 0)) (hh2 : 0 ≤ deriv^[2] h (q 0)) :
    warpedMetric f h q (modelCurv (warpedMetric f h) q u v v) u ≤ 0 := by
  rw [warped_sec_eq f h q u v hf hh hf0 hh0]
  -- each of the four coefficients in the explicit formula is non-negative
  have hA : 0 ≤ f (q 0) * deriv^[2] f (q 0) := mul_nonneg (le_of_lt hf0) hf2
  have hB : 0 ≤ h (q 0) * deriv^[2] h (q 0) := mul_nonneg (le_of_lt hh0) hh2
  have hC : 0 ≤ f (q 0) * h (q 0) * deriv f (q 0) * deriv h (q 0) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hf0) (le_of_lt hh0)) hf1) hh1
  have hD : 0 ≤ h (q 0) ^ 2 * deriv h (q 0) ^ 2 :=
    mul_nonneg (sq_nonneg (h (q 0))) (sq_nonneg (deriv h (q 0)))
  -- hence each of the four summands is non-negative, being a coefficient times a square
  have t1 : 0 ≤ f (q 0) * deriv^[2] f (q 0) * (u 0 * v 1 - u 1 * v 0) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  have t2 : 0 ≤ h (q 0) * deriv^[2] h (q 0)
      * ((u 0 * v 2 - u 2 * v 0) ^ 2 + (u 0 * v 3 - u 3 * v 0) ^ 2) :=
    mul_nonneg hB (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have t3 : 0 ≤ f (q 0) * h (q 0) * deriv f (q 0) * deriv h (q 0)
      * ((u 1 * v 2 - u 2 * v 1) ^ 2 + (u 1 * v 3 - u 3 * v 1) ^ 2) :=
    mul_nonneg hC (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have t4 : 0 ≤ h (q 0) ^ 2 * deriv h (q 0) ^ 2 * (u 2 * v 3 - u 3 * v 2) ^ 2 :=
    mul_nonneg hD (sq_nonneg _)
  linarith

end Work.Curvature
