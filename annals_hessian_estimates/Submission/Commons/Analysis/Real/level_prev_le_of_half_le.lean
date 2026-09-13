import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Real

theorem level_prev_le_of_half_le {a M : ℝ} (ha : 1 / 2 ≤ a) (hM : 2 ≤ M) {k : ℕ} (hk : 1 ≤ k) :
    1 + 2 * a * M ^ (k - 1) ≤ 2 * (1 + 2 * a * M ^ k) / M := by
  -- Clear the denominator: it suffices to show the inequality multiplied through by `M > 0`.
  have hMpos : 0 < M := by linarith
  rw [le_div_iff₀ hMpos]
  -- Relate `M ^ k` with `M ^ (k-1) * M` (valid since `k ≥ 1`).
  have hkpos : 0 < k := by omega
  have hk1 : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos hkpos).symm
  have hpow : M ^ k = M ^ (k - 1) * M := by
    conv_lhs => rw [hk1]
    rw [pow_succ', mul_comm]
  rw [hpow]
  -- Now reduce to `M - 2 ≤ 2 * a * M^(k-1) * M`, which holds because
  -- `2a ≥ 1`, `M^(k-1) ≥ 1`, `M ≥ 0`.
  have ht : (1 : ℝ) ≤ M ^ (k - 1) := one_le_pow₀ (by linarith : (1 : ℝ) ≤ M)
  have ht0 : (0 : ℝ) ≤ M ^ (k - 1) := by linarith
  have hA : (0 : ℝ) ≤ 2 * a * M ^ (k - 1) - 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * a - 1) ht0]
  have hM0 : (0 : ℝ) ≤ M := by linarith
  nlinarith [mul_nonneg hA hM0]

end Commons.Analysis.Real