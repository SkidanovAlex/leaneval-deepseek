import Mathlib

namespace Work.Asymptotics

/-- Jacobi's one-variable theta function, expanded as a power series in `q = exp (π i z)`. -/
theorem theta00_pow_series (z : ℂ) (hz : 0 < z.im) :
    jacobiTheta z = 1 + 2 * ∑' n : ℕ, (Complex.exp (Real.pi * Complex.I * z)) ^ ((n + 1) ^ 2) := by
  have hsum : (∑' n : ℕ, Complex.exp (↑Real.pi * Complex.I * (↑n + 1) ^ 2 * z))
      = ∑' n : ℕ, (Complex.exp (Real.pi * Complex.I * z)) ^ ((n + 1) ^ 2) := by
    apply tsum_congr
    intro n
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [jacobiTheta_eq_tsum_nat hz, hsum]

end Work.Asymptotics
