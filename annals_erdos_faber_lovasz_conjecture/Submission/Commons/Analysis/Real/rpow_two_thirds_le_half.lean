import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

/-- For `n ≥ 8`, the exponent `2/3` grows slower than the linear factor `1/2`:
`n^(2/3) ≤ n/2`. -/
theorem rpow_two_thirds_le_half (n : ℕ) (hn : 8 ≤ n) :
    Real.rpow (n : ℝ) (2 / 3) ≤ (n : ℝ) / 2 := by
  -- Switch to `^`-notation so the standard `rpow` rewrite lemmas apply.
  change (n : ℝ) ^ ((2 : ℝ) / 3) ≤ (n : ℝ) / 2
  have hx8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < (n : ℝ) := by linarith
  -- `3 * log 2 = log 8 ≤ log n`, since `8 ≤ n`.
  have hlog : 3 * Real.log 2 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (show (0 : ℝ) < 8 by norm_num) hx8
    rwa [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, Real.log_pow] at h
  -- Consequently `(2/3) * log n ≤ log n - log 2`.
  have key : Real.log (n : ℝ) * (2 / 3 : ℝ) ≤ Real.log (n : ℝ) - Real.log 2 := by
    nlinarith [hlog]
  -- Both sides are exponentials; compare the exponents.
  rw [Real.rpow_def_of_pos hx0]
  rw [← Real.exp_log (show (0 : ℝ) < (n : ℝ) / 2 by linarith),
      Real.log_div (ne_of_gt hx0) (by norm_num : (2 : ℝ) ≠ 0)]
  exact Real.exp_le_exp.mpr key

end Commons.Analysis.Real