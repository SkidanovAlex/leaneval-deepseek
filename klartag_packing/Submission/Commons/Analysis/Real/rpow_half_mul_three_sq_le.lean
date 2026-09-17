import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum.RealSqrt

namespace Commons.Analysis.Real

theorem rpow_half_mul_three_sq_le (x : ℝ) (hx : 0 ≤ x) :
    x ^ (1 / 2 : ℝ) * (3 * x ^ 2) ^ (1 / 2 : ℝ) ≤ 3 * x ^ (3 / 2 : ℝ) := by
  have h3x2 : (0:ℝ) ≤ 3 * x^2 := by positivity
  have hx3 : (0:ℝ) ≤ x^3 := by positivity
  -- Rewrite the left-hand side as a single half-power: x^{1/2} (3x²)^{1/2} = (3x³)^{1/2}.
  have h1 : x ^ (1/2:ℝ) * (3 * x^2) ^ (1/2:ℝ) = (3 * x^3) ^ (1/2:ℝ) := by
    rw [← Real.mul_rpow hx h3x2]
    congr 1
    ring
  rw [h1]
  -- Monotonicity of the half-power applied to 3x³ ≤ 9x³.
  have h2 : (3 * x^3) ^ (1/2:ℝ) ≤ (9 * x^3) ^ (1/2:ℝ) := by
    apply Real.rpow_le_rpow (by positivity)
    · nlinarith
    · norm_num
  -- (9x³)^{1/2} = 3 x^{3/2}.
  have h3 : (9 * x^3:ℝ) ^ (1/2:ℝ) = 3 * x ^ (3/2:ℝ) := by
    rw [Real.mul_rpow (show (0:ℝ) ≤ 9 by norm_num) hx3]
    have h9 : (9:ℝ) ^ (1/2:ℝ) = 3 := by
      rw [← Real.sqrt_eq_rpow]; norm_num
    have hx9 : (x^3:ℝ) ^ (1/2:ℝ) = x ^ (3/2:ℝ) := by
      have hcast : (x^3:ℝ) = x ^ (3:ℝ) := (Real.rpow_natCast x 3).symm
      rw [hcast, ← Real.rpow_mul hx (3:ℝ) (1/2:ℝ),
          show (3:ℝ)*(1/2:ℝ) = 3/2 by norm_num]
    rw [h9, hx9]
  linarith [h2, h3.le]

end Commons.Analysis.Real