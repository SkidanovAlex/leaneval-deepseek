import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- For a point `y` of the open unit ball the factor `1 - ‖y‖²` is positive, so the Klein lift
`hypOfKlein` is well defined and its normalisation factor `(√(1-‖y‖²))⁻¹` is nonzero. -/
theorem one_sub_norm_sq_pos_of_mem_ball {y : E4} (hy : y ∈ ball) : 0 < 1 - ‖y‖ ^ 2 := by
  simp [ball] at hy
  nlinarith [norm_nonneg y]

/-- The normalising factor of the Klein lift is nonzero on the ball. -/
theorem sqrt_one_sub_norm_sq_ne_zero_of_mem_ball {y : E4} (hy : y ∈ ball) :
    Real.sqrt (1 - ‖y‖ ^ 2) ≠ 0 :=
  (Real.sqrt_ne_zero').mpr (one_sub_norm_sq_pos_of_mem_ball hy)

/-- **`kleinOfHyp` is a left inverse of `hypOfKlein`.**  The central projection on the plane
`x₄ = 1` undoes the Klein lift: for `y` in the open unit ball,
`kleinOfHyp (hypOfKlein y) = y`. -/
theorem kleinOfHyp_hypOfKlein {y : E4} (hy : y ∈ ball) : kleinOfHyp (hypOfKlein y) = y := by
  have hs : Real.sqrt (1 - ‖y‖ ^ 2) ≠ 0 := sqrt_one_sub_norm_sq_ne_zero_of_mem_ball hy
  ext i
  fin_cases i <;>
    simp [kleinOfHyp, hypOfKlein, ray, hs]

end Work.HypModel
