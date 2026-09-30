import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The `σ_v`-component of the `y`-part `cuspY v y = y₀λ₂ + y₁λ₃` of a cusp coordinate: since
`(κ_{v,1},κ_{v,2},κ_{v,3})` is an orthogonal basis and `σ_v = κ_{v,1} + b_v κ_{v,2}`, only the
`κ_{v,2}`-component survives, giving `⟨cuspY v y, σ_v⟩ = b_v ‖κ_{v,2}‖² y₀`. -/
theorem slope_dot_cuspY (v : Fin 5) (y : E2) :
    inner ℝ (cuspY v y) (slope v) = (slopeB v : ℝ) * ‖kv v 1‖ ^ 2 * y 0 := by
  fin_cases v <;> simp only [cuspY, slope, lam2, lam3, kv, kappa, slopeB, slopeC]
  all_goals
    simp [PiLp.inner_apply, Fin.sum_univ_three, PiLp.norm_sq_eq_of_L2]
    ring

end Work.Cusp
