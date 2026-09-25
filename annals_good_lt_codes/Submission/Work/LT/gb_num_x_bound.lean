import Mathlib

namespace Work.LT

/-- Tail bound for the geometric series estimate: for `0 < x ≤ 3/5`,
`4*x^7 + 4*x^6/(1-x) ≤ x`. (Both `f(x) = 4x^7 + 4x^6/(1-x)` and `f(x)/x = 4x^6 + 4x^5/(1-x)` are
increasing on `(0,1)`, and `f(3/5)/(3/5) = 0.964... ≤ 1`.) -/
theorem gb_num_x_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 3/5) :
    (4:ℝ) * x^7 + 4 * x^6 / (1 - x) ≤ x := by
  -- `x ≤ 3/5` gives `1 - x ≥ 2/5 > 0`.
  have h1x : 0 < 1 - x := by linarith
  have h1x' : (2:ℝ)/5 ≤ 1 - x := by linarith
  have hx6 : (0:ℝ) ≤ x^6 := by positivity
  -- Step 1: `4*x^6/(1-x) ≤ 10*x^6`.
  have hdiv : 4 * x^6 / (1 - x) ≤ 10 * x^6 := by
    rw [div_le_iff₀ h1x]
    nlinarith [h1x', hx6]
  -- Step 2: `4*x^6 + 10*x^5 ≤ 1`, by monotonicity of powers and a numeric bound at `3/5`.
  have h5 : x^5 ≤ (3/5:ℝ)^5 := pow_le_pow_left₀ (le_of_lt hx0) hx1 5
  have h6 : x^6 ≤ (3/5:ℝ)^6 := pow_le_pow_left₀ (le_of_lt hx0) hx1 6
  have hp : (4:ℝ) * x^6 + 10 * x^5 ≤ 1 := by
    have e1 := mul_le_mul_of_nonneg_left h6 (by norm_num : (0:ℝ) ≤ 4)
    have e2 := mul_le_mul_of_nonneg_left h5 (by norm_num : (0:ℝ) ≤ 10)
    have hn : (4:ℝ) * (3/5)^6 + 10 * (3/5)^5 ≤ 1 := by norm_num
    linarith
  -- Step 3: multiply by `x > 0` to get `4*x^7 + 10*x^6 ≤ x`.
  have hmain : (4:ℝ) * x^7 + 10 * x^6 ≤ x := by
    have e3 := mul_le_mul_of_nonneg_left hp (le_of_lt hx0)
    nlinarith [e3]
  linarith

end Work.LT
