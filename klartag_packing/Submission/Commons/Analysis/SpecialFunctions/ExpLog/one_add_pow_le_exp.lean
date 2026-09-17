import Mathlib.Analysis.Complex.Exponential

namespace Commons.Analysis.SpecialFunctions.ExpLog

theorem one_add_pow_le_exp (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ n ≤ Real.exp ((n : ℝ) * x) := by
  have hnonneg : (0 : ℝ) ≤ 1 + x := by linarith
  have hle : (1 : ℝ) + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  calc
    (1 + x) ^ n ≤ (Real.exp x) ^ n := pow_le_pow_left₀ hnonneg hle n
    _ = Real.exp ((n : ℝ) * x) := (Real.exp_nat_mul x n).symm

end Commons.Analysis.SpecialFunctions.ExpLog