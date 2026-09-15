import Mathlib.Data.Real.Basic

namespace Commons.Analysis.Real

theorem inv_pow_prod_two (n N k : ℕ) :
    ((2 : ℝ) ^ k * ((2 : ℝ) ^ N)⁻¹) ^ n =
      (2 : ℝ) ^ (n * k) * ((2 : ℝ) ^ (n * N))⁻¹ := by
  rw [mul_pow, inv_pow]
  simp only [← pow_mul]
  rw [Nat.mul_comm k n, Nat.mul_comm N n]

end Commons.Analysis.Real