import Mathlib

namespace Work.Resample

theorem exp_nat_le_two_pow (n : ℕ) : Real.exp (n : ℝ) ≤ (2:ℝ)^(2*n) := by
  have h1 : Real.exp (n : ℝ) = (Real.exp 1)^n := by simp
  rw [h1]
  have h4 : Real.exp 1 ≤ (4:ℝ) := by linarith [Real.exp_one_lt_d9]
  calc (Real.exp 1)^n ≤ (4:ℝ)^n := by gcongr
    _ = (2:ℝ)^(2*n) := by rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul]

end Work.Resample
