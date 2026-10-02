import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Angle

/-- Angle doubling on `ℝ` and on `ℚ` agree under the coercion `ℚ → ℝ`.
This is the rational-cast compatibility of `Int.fract` (`Rat.cast_fract`). -/
theorem angDouble_coe_rat (q : ℚ) :
    Work.Landing.angDouble (q : ℝ) = ((Work.Landing.angDoubleQ q : ℚ) : ℝ) := by
  simp only [Work.Landing.angDouble, Work.Landing.angDoubleQ]
  have h : ((Int.fract (-2 * q) : ℚ) : ℝ) = Int.fract (((-2 * q : ℚ) : ℝ)) :=
    Rat.cast_fract (-2 * q)
  rw [show ((-2 * q : ℚ) : ℝ) = -2 * (q : ℝ) by push_cast; ring] at h
  exact h.symm

end Work.Landing.Angle
