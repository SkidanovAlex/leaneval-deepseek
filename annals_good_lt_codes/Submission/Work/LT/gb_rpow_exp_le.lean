import Mathlib

namespace Work.LT

/-- Exponent inequality behind Kalachev--Panteleev Lemma 4: for `r ≥ 2` the bound `2^{2rD - r(r-1)/2}` is at most `2^{2rD - r^2/4}`. -/
theorem gb_rpow_exp_le (D r : ℕ) (hr : 2 ≤ r) :
    (2 : ℝ) ^ (2 * (r : ℝ) * (D : ℝ) - (r : ℝ) * ((r : ℝ) - 1) / 2) ≤
      (2 : ℝ) ^ (2 * (r : ℝ) * (D : ℝ) - (r : ℝ) ^ 2 / 4) := by
  -- base `2 > 1` is monotone, so it suffices to compare the exponents
  refine (Real.rpow_le_rpow_left_iff (x := 2) (by norm_num : (1:ℝ) < 2)).mpr ?_
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
  -- both exponents share the term `2rD`; the claim reduces to `r(r-1)/2 ≥ r^2/4`,
  -- i.e. `r^2 - 2r = r(r-2) ≥ 0`, which holds for `r ≥ 2`.
  nlinarith [mul_nonneg hr0 (by linarith : (0:ℝ) ≤ (r:ℝ) - 2)]

end Work.LT
