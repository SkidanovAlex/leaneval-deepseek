import Mathlib

namespace Work.LinnikAreas.Density4

/-- Pointwise prime-weight comparison (Linnik, Density4):

    `2 / (n (n-1)) * sqrt n ≤ 8 (1/sqrt(n-1) - 1/sqrt n)` for `n ≥ 2`.

    Writing `a = sqrt (n-1)`, `b = sqrt n` (so `a,b > 0`, `b^2 = a^2 + 1`),
    the left side is `2/(b a^2)` and the right side is `8/(a b (a+b))`,
    so the claim reduces to `b ≤ 3a`, i.e. `n ≤ 9(n-1)`. -/
theorem prime_weight_pointwise (n : ℕ) (hn : 2 ≤ n) :
    2 / ((n : ℝ) * ((n : ℝ) - 1)) * Real.sqrt (n : ℝ) ≤
      8 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN : (0 : ℝ) < (n : ℝ) := by linarith only [hn2]
  have hN1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith only [hn2]
  set a := Real.sqrt ((n : ℝ) - 1) with ha_def
  set b := Real.sqrt (n : ℝ) with hb_def
  have ha : 0 < a := by rw [ha_def]; exact Real.sqrt_pos.mpr hN1
  have hb : 0 < b := by rw [hb_def]; exact Real.sqrt_pos.mpr hN
  have hsa : a ^ 2 = (n : ℝ) - 1 := by rw [ha_def]; exact Real.sq_sqrt (le_of_lt hN1)
  have hsb : b ^ 2 = (n : ℝ) := by rw [hb_def]; exact Real.sq_sqrt (le_of_lt hN)
  -- Key inequality `b ≤ 3a`, equivalently `n ≤ 9 (n - 1)`.
  have hba : b ≤ 3 * a := by
    have h2 : b ^ 2 ≤ (3 * a) ^ 2 := by
      rw [hsb, mul_pow, hsa]
      linarith only [hn2]
    have h3 := sq_le_sq.mp h2
    rw [abs_of_nonneg (le_of_lt hb), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * a)] at h3
    exact h3
  -- `1/a - 1/b = 1/(a b (a+b))`.
  have hR : (1 / a - 1 / b) = 1 / (a * b * (a + b)) := by
    field_simp
    linarith only [hsb, hsa]
  -- `2/(n (n-1)) * b = 2/(b a^2)`.
  have hL : 2 / (b ^ 2 * a ^ 2) * b = 2 / (b * a ^ 2) := by
    field_simp
  rw [← hsa, ← hsb, hR, hL, mul_one_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith only [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * a * b)
    (by linarith : (0 : ℝ) ≤ 3 * a - b)]

end Work.LinnikAreas.Density4
