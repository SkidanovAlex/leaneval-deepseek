import Mathlib

namespace Work.ZeroDensity.Jutila.LzAux

/-- For `1 ≤ r`, the square `(1 + log r)^2` is at most `25 * sqrt r`.  This is a very
generous form of the elementary bound `log x ≤ x^ε/ε`: taking `ε = 1/4` gives
`log r ≤ 4 r^(1/4)`, whence `1 + log r ≤ 5 r^(1/4)` (using `1 ≤ r^(1/4)`), and
squaring yields `(1 + log r)^2 ≤ 25 r^(1/2) = 25 sqrt r`. -/
theorem CzLogSqLe (r : ℝ) (hr : 1 ≤ r) : (1 + Real.log r) ^ 2 ≤ 25 * Real.sqrt r := by
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  -- `log r ≤ 4 * r^(1/4)`, from `log x ≤ x^ε / ε` with `ε = 1/4`.
  have hlog : Real.log r ≤ 4 * r ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div (x := r) (ε := (1 / 4 : ℝ)) hr0 (by norm_num)
    have hdiv : r ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * r ^ (1 / 4 : ℝ) := by ring
    linarith [h, hdiv.le]
  -- `1 ≤ r^(1/4)` since `r ≥ 1`.
  have hpow : (1 : ℝ) ≤ r ^ (1 / 4 : ℝ) := Real.one_le_rpow hr (by norm_num)
  have hsum : 1 + Real.log r ≤ 5 * r ^ (1 / 4 : ℝ) := by linarith
  have hnn : 0 ≤ 1 + Real.log r := by
    have := Real.log_nonneg hr
    linarith
  have hsq : (1 + Real.log r) ^ 2 ≤ (5 * r ^ (1 / 4 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hnn hsum 2
  -- `(r^(1/4))^2 = r^(1/2) = sqrt r`.
  have hsqrt : (r ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt r := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (r ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hr0]
    norm_num
  calc (1 + Real.log r) ^ 2 ≤ (5 * r ^ (1 / 4 : ℝ)) ^ 2 := hsq
    _ = 25 * (r ^ (1 / 4 : ℝ)) ^ 2 := by ring
    _ = 25 * Real.sqrt r := by rw [hsqrt]

end Work.ZeroDensity.Jutila.LzAux
