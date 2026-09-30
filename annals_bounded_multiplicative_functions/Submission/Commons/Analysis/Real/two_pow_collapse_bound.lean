import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Real

theorem two_pow_collapse_bound (n k : ℕ) :
    ((2 : ℝ) ^ (n + 1) + 1) ^ k ≤ (4 : ℝ) ^ k * (2 : ℝ) ^ (n * k) := by
  have hA1 : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
  have hbase : (2 : ℝ) ^ (n + 1) + 1 ≤ (2 : ℝ) ^ (n + 2) := by
    calc
      (2 : ℝ) ^ (n + 1) + 1 ≤ (2 : ℝ) ^ (n + 1) + (2 : ℝ) ^ (n + 1) := by
        gcongr
      _ = (2 : ℝ) ^ (n + 2) := by
        rw [← two_mul, ← pow_succ']
  calc
    ((2 : ℝ) ^ (n + 1) + 1) ^ k ≤ ((2 : ℝ) ^ (n + 2)) ^ k := by
      exact pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ (n + 1) + 1) hbase k
    _ = (2 : ℝ) ^ ((n + 2) * k) := by
      rw [pow_mul]
    _ = (2 : ℝ) ^ (2 * k + n * k) := by
      congr 1
      ring
    _ = (2 : ℝ) ^ (2 * k) * (2 : ℝ) ^ (n * k) := by
      rw [pow_add]
    _ = ((2 : ℝ) ^ 2) ^ k * (2 : ℝ) ^ (n * k) := by
      rw [pow_mul]
    _ = (4 : ℝ) ^ k * (2 : ℝ) ^ (n * k) := by
      norm_num

end Commons.Analysis.Real
