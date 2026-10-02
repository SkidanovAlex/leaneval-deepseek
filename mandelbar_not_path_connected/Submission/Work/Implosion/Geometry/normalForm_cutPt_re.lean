import Mathlib
import Submission.Work.Implosion.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Geometry

open Complex

/-- The cut point `t·(λi)` seen as a real multiple of `I`, hence purely imaginary. -/
theorem cutPt_mul_I (lam t : ℝ) :
    cutPt ((lam : ℂ) * I) t = ((t * lam : ℝ) : ℂ) * I := by
  simp only [cutPt, Complex.ofReal_mul]
  ring

/-- The real factor `ζ^2 - a^2` at `ζ = t·a` with `a = λi` equals `λ²(1-t²)`. -/
theorem cutPt_quad_factor (lam t : ℝ) :
    (((t : ℂ) ^ 2 - 1) * (((lam : ℂ) * I) ^ 2))
      = ((lam ^ 2 * (1 - t ^ 2) : ℝ) : ℂ) := by
  have hI2 : I ^ 2 = (-1 : ℂ) := by rw [pow_two, Complex.I_mul_I]
  have : ((lam : ℂ) * I) ^ 2 = -((lam : ℂ) ^ 2) := by
    rw [mul_pow, hI2]; ring
  rw [this]
  push_cast
  ring

theorem normalForm_cutPt_re (lam : ℝ) (h : ℂ → ℂ) (t : ℝ) :
    (normalForm ((lam : ℂ) * I) h (cutPt ((lam : ℂ) * I) t)).re
      = lam ^ 2 * (1 - t ^ 2) * (h (cutPt ((lam : ℂ) * I) t)).re := by
  rw [normalForm_apply_cutPt, cutPt_quad_factor, cutPt_mul_I,
    Complex.add_re, Complex.mul_I_re, Complex.ofReal_im, Complex.re_ofReal_mul]
  ring

end Work.Implosion.Geometry
