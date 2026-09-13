import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Real

theorem theta_le_fifteen_sixteenth {M K : ℝ} (hM : 1 < M) (hK : 1 ≤ K) :
    ((M - 1) / (8 * M)) ^ 4 / (K ^ 4 * 5 ^ 4) ≤ 15 / 16 := by
  have hMpos : (0 : ℝ) < M := by linarith
  have hbase_nonneg : (0 : ℝ) ≤ (M - 1) / (8 * M) := by positivity
  have hbase_le : (M - 1) / (8 * M) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * M)]
    linarith
  have hpow : ((M - 1) / (8 * M)) ^ 4 ≤ (1 / 8) ^ 4 :=
    pow_le_pow_left₀ hbase_nonneg hbase_le 4
  have hK4 : (1 : ℝ) ≤ K ^ 4 := one_le_pow₀ hK
  have hD0 : 0 < K ^ 4 * 5 ^ 4 := by positivity
  have hDle : (1 : ℝ) * 5 ^ 4 ≤ K ^ 4 * 5 ^ 4 := by nlinarith [hK4]
  have hstep : ((M - 1) / (8 * M)) ^ 4 / (K ^ 4 * 5 ^ 4) ≤ (1 / 8) ^ 4 / ((1 : ℝ) * 5 ^ 4) :=
    div_le_div₀ (by positivity) hpow (by norm_num) hDle
  have hnum : (1 / 8 : ℝ) ^ 4 / ((1 : ℝ) * 5 ^ 4) ≤ 15 / 16 := by norm_num
  linarith

end Commons.Analysis.Real