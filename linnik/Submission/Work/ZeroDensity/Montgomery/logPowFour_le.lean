import Mathlib

namespace Work.ZeroDensity.Montgomery

theorem logPowFour_le (N : ℕ) (hN : 1 ≤ N) :
    (1 + Real.log (N : ℝ)) ^ 4 ≤ 16 * (Real.log (2 * (N : ℝ))) ^ 4 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by linarith
    linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmul : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0]
  have hle : 1 + Real.log (N : ℝ) ≤ 2 * Real.log (2 * (N : ℝ)) := by
    rw [hmul]; linarith
  have hpow := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + Real.log (N : ℝ)) hle 4
  calc (1 + Real.log (N : ℝ)) ^ 4 ≤ (2 * Real.log (2 * (N : ℝ))) ^ 4 := hpow
    _ = 16 * (Real.log (2 * (N : ℝ))) ^ 4 := by ring

end Work.ZeroDensity.Montgomery
