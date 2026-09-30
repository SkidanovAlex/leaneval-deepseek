import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.InnerProductSpace

/-- Expansion of the squared norm of a linear combination `r • u + s • v` in a real inner
product space. -/
lemma norm_sq_smul_add_smul {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u v : F) (r s : ℝ) :
    ‖r • u + s • v‖ ^ 2 = r ^ 2 * ‖u‖ ^ 2 + 2 * r * s * inner ℝ u v + s ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  ring

theorem norm_sq_polar_decomp {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A A' : F) (c c' : ℝ) (hunit : norm A ^ 2 + c ^ 2 = 1) (hne : A ≠ 0)
    (htan : inner ℝ A' A + c' * c = 0) :
    norm A' ^ 2 + c' ^ 2 = (c' / norm A) ^ 2
      + norm A ^ 2 * norm ((norm A)⁻¹ • A' + ((c * c') / norm A ^ 3) • A) ^ 2 := by
  have hA : (‖A‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hne
  have hinner : inner ℝ A' A = -(c' * c) := by linarith
  have key : (‖A‖ : ℝ) ^ 4 * ‖(‖A‖)⁻¹ • A' + ((c * c') / ‖A‖ ^ 3) • A‖ ^ 2
      = (‖A‖) ^ 2 * ‖A'‖ ^ 2 - c ^ 2 * c' ^ 2 := by
    rw [norm_sq_smul_add_smul A' A (‖A‖)⁻¹ ((c * c') / ‖A‖ ^ 3), hinner]
    field_simp
    ring
  have hc : (‖A‖ : ℝ) ^ 2 * (c' / ‖A‖) ^ 2 = c' ^ 2 := by
    rw [div_pow]
    field_simp
  have h2 : (‖A‖ : ℝ) ^ 2 * (‖A'‖ ^ 2 + c' ^ 2)
      = (‖A‖) ^ 2 * ((c' / ‖A‖) ^ 2
          + (‖A‖) ^ 2 * ‖(‖A‖)⁻¹ • A' + ((c * c') / ‖A‖ ^ 3) • A‖ ^ 2) := by
    rw [mul_add, mul_add, hc]
    have hkey' : (‖A‖ : ℝ) ^ 2
          * ((‖A‖) ^ 2 * ‖(‖A‖)⁻¹ • A' + ((c * c') / ‖A‖ ^ 3) • A‖ ^ 2)
        = (‖A‖) ^ 2 * ‖A'‖ ^ 2 - c ^ 2 * c' ^ 2 := by
      have hh : (‖A‖ : ℝ) ^ 2
            * ((‖A‖) ^ 2 * ‖(‖A‖)⁻¹ • A' + ((c * c') / ‖A‖ ^ 3) • A‖ ^ 2)
          = (‖A‖) ^ 4 * ‖(‖A‖)⁻¹ • A' + ((c * c') / ‖A‖ ^ 3) • A‖ ^ 2 := by ring
      rw [hh, key]
    nlinarith [hkey', hunit]
  exact mul_left_cancel₀ (pow_ne_zero 2 hA) h2

end Commons.Analysis.InnerProductSpace