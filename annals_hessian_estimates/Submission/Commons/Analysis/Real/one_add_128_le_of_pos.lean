import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.Analysis.Real

theorem one_add_128_le_of_pos {p : ℝ} (hp : 0 < p) :
    (4 : ℝ) ≤ 1 + 128 * ((1 / p) * (2 ^ p - 1)) := by
  have h2 : (2 : ℝ) ^ p = Real.exp (Real.log 2 * p) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hexp : Real.log 2 * p + 1 ≤ (2 : ℝ) ^ p := by
    rw [h2]; exact Real.add_one_le_exp _
  have hsub : Real.log 2 * p ≤ (2 : ℝ) ^ p - 1 := by linarith
  have hlog : (3 : ℝ) / 128 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hstep : Real.log 2 ≤ (2 ^ p - 1) / p := by
    rw [le_div_iff₀ hp]; linarith
  have hkey : (3 : ℝ) ≤ 128 * ((1 / p) * (2 ^ p - 1)) := by
    have h1 : (128 : ℝ) * Real.log 2 ≤ 128 * ((1 / p) * (2 ^ p - 1)) := by
      rw [show (1 / p) * (2 ^ p - 1) = (2 ^ p - 1) / p by ring]
      exact mul_le_mul_of_nonneg_left hstep (by norm_num)
    nlinarith [h1, hlog]
  linarith

end Commons.Analysis.Real