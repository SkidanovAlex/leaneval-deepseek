import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Real

lemma mul_le_mul_pow_of_le {n d : ℕ} {s ε M : ℝ} (hn : n ≤ d) (hs : s ≤ ε) (hM : 1 ≤ M)
    (hs0 : 0 ≤ s) (hε0 : 0 ≤ ε) :
    (n + 1 : ℝ) * s * M ^ n ≤ (d + 1 : ℝ) * ε * M ^ d := by
  have hM0 : 0 ≤ M := by linarith
  have hd1 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  have hnd : (n + 1 : ℝ) ≤ (d + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hn
  have hp : M ^ n ≤ M ^ d := pow_le_pow_right₀ hM hn
  have hεE : 0 ≤ (d + 1 : ℝ) * ε := mul_nonneg hd1 hε0
  calc (n + 1 : ℝ) * s * M ^ n
      = ((n + 1 : ℝ) * s) * M ^ n := by ring
    _ ≤ ((d + 1 : ℝ) * s) * M ^ n := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnd hs0) (pow_nonneg hM0 n)
    _ = (d + 1 : ℝ) * (s * M ^ n) := by ring
    _ ≤ (d + 1 : ℝ) * (ε * M ^ n) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (pow_nonneg hM0 n)) hd1
    _ = ((d + 1 : ℝ) * ε) * M ^ n := by ring
    _ ≤ ((d + 1 : ℝ) * ε) * M ^ d := by
        exact mul_le_mul_of_nonneg_left hp hεE
    _ = (d + 1 : ℝ) * ε * M ^ d := by ring

end Commons.Analysis.Real