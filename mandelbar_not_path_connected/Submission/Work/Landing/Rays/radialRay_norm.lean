import Mathlib
import Submission.Work.Landing.Rays

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Rays

/-- The direction `rayDirection θ = e^{2πiθ}` has modulus one. -/
theorem norm_rayDirection (θ : ℝ) : ‖rayDirection θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (2 * Real.pi * θ)

/-- Every point of the radial line of angle `θ` lies outside the closed unit disk: the radial
line is `{r e^{2πiθ} : r > 1}`, and `‖e^{2πiθ}‖ = 1`. -/
theorem radialRay_norm {θ : ℝ} {w : ℂ} (hw : w ∈ Work.Landing.radialRay θ) : 1 < ‖w‖ := by
  rcases hw with ⟨r, hr, rfl⟩
  rw [norm_mul, norm_rayDirection, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]
  exact hr

end Work.Landing.Rays
