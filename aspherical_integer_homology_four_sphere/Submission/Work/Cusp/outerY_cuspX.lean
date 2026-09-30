import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

open scoped Real InnerProductSpace

set_option linter.unnecessarySeqFocus false

/-- **`outerY` is a left inverse of `cuspX`.**  In the cusp coordinates `x = u σ_v + y₂λ₂ + y₃λ₃`
the vector `(κ_{v,1}, κ_{v,2}, κ_{v,3})` is an orthogonal basis of `ℝ³` with
`σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}` and `c_v = 0`.  Hence the `κ_{v,1}`-coordinate of `x`
is `u`, the `κ_{v,2}`-coordinate of `x` is `b_v u + y₂`, and the `κ_{v,3}`-coordinate is `y₃`;
`outerY v x = (⟪x,κ_{v,2}⟫/‖κ_{v,2}‖² − b_v ⟪x,κ_{v,1}⟫/‖κ_{v,1}‖², ⟪x,κ_{v,3}⟫/‖κ_{v,3}‖²)`
recovers exactly `(y₂,y₃)`.  Everything is a finite computation on the explicit integer data
`kappa`, `slopeB`, `slopeC`, so we check the five cusps separately. -/
theorem outerY_cuspX (v : Fin 5) (s : ℝ) (y : E2) : outerY v (cuspX v s y) = y := by
  fin_cases v
  all_goals
    simp only [outerY, cuspX, cuspY, slope, lam2, lam3, kv, outerU, kappaCoord, kappa, slopeB,
      slopeC]
    ext i <;> fin_cases i <;>
      (simp [Fin.sum_univ_three, PiLp.inner_apply, EuclideanSpace.norm_eq, Fin.isValue]; ring)

end Work.Cusp
