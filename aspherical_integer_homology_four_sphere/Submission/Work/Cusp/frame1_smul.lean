import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `frame1 v = σ̂_v = ‖σ_v‖⁻¹ • σ_v` is the unit vector along the slope, so `‖σ_v‖ • frame1 v = σ_v`.
The identity is unconditional: if `‖σ_v‖ = 0` then `σ_v = 0` and both sides vanish. -/
theorem frame1_smul (v : Fin 5) : ‖slope v‖ • frame1 v = slope v := by
  unfold frame1
  rw [smul_smul]
  rcases eq_or_ne ‖slope v‖ 0 with h | h
  · rw [h, zero_mul, zero_smul]
    exact (norm_eq_zero.mp h).symm
  · rw [mul_inv_cancel₀ h, one_smul]

end Work.Cusp
