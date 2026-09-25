import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace Commons.Analysis.ENNReal

/-- For `x y : ℝ≥0∞`, `(x + y) ^ (2 : ℝ) ≤ 2 * x ^ (2 : ℝ) + 2 * y ^ (2 : ℝ)`.
This is the `p = 2` case of the parallelogram inequality `(x + y) ^ 2 ≤ 2 (x ^ 2 + y ^ 2)`,
stated for the real power on `ℝ≥0∞`. -/
theorem add_rpow_two_le_two_mul (x y : ENNReal) :
    (x + y) ^ (2:ℝ) ≤ 2 * x ^ (2:ℝ) + 2 * y ^ (2:ℝ) := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  have hxy : x + y ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hx, hy⟩
  have hx2 : x ^ (2:ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hx
  have hy2 : y ^ (2:ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hy
  have h2x : 2 * x ^ (2:ℝ) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hx2
  have h2y : 2 * y ^ (2:ℝ) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hy2
  rw [← ENNReal.toReal_le_toReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hxy)
        (ENNReal.add_ne_top.mpr ⟨h2x, h2y⟩)]
  rw [ENNReal.toReal_add h2x h2y, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat 2,
      ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
      ENNReal.toReal_add hx hy]
  rw [Real.rpow_two, Real.rpow_two, Real.rpow_two]
  nlinarith [sq_nonneg (x.toReal - y.toReal)]

end Commons.Analysis.ENNReal