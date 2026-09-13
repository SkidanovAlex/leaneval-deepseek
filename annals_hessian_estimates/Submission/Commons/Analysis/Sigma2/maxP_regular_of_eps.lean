import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Sigma2

/-- Elementary algebraic comparison used in the regularity step for the maximal
function `P` in the σ₂-equation: if `A + (eps / b) * D - (1 / b ^ 2) * D ≤ 0`
with `36 ≤ b`, `0 ≤ D` and `1 / 18 ≤ eps`, then the same expression with the
exponent `1 / b` replaced by the universal constant `1 / 36` is still `≤ 0`. -/
theorem maxP_regular_of_eps {eps b D A : ℝ} (hb : 36 ≤ b) (hD : 0 ≤ D) (heps : 1 / 18 ≤ eps)
    (h : A + (eps / b) * D - (1 / b ^ 2) * D ≤ 0) : A + (1 / 36) * ((1 / b) * D) ≤ 0 := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hmul : (1 / 18 : ℝ) * b ≤ eps * b := mul_le_mul_of_nonneg_right heps (le_of_lt hb0)
  have key : (1 / 36) * ((1 / b) * D) ≤ (eps / b) * D - (1 / b ^ 2) * D := by
    field_simp
    nlinarith [hb, heps, hD, hmul]
  linarith

end Commons.Analysis.Sigma2