import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Combinatorics.EFLArith

theorem sixth_arith {ε : ℝ} {n : ℕ} (hεs : 1000 * ε ≤ 1) :
    (n : ℝ) / 7 ≤ (n : ℝ) / 6 - ε * n := by
  have hε : ε ≤ 1 / 42 := by linarith
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h : ε * (n : ℝ) ≤ (1 / 42) * (n : ℝ) := mul_le_mul_of_nonneg_right hε hn
  nlinarith [h]

end Commons.Combinatorics.EFLArith