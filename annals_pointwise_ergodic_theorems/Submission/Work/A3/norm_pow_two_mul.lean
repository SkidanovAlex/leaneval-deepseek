import Mathlib

namespace Work.A3

theorem norm_pow_two_mul (z : ℂ) (k : ℕ) : ‖z‖ ^ (2 * k) = (z ^ k * (starRingEnd ℂ) (z ^ k)).re := by
  have h1 : z ^ k * (starRingEnd ℂ) (z ^ k) = (((Complex.normSq z) ^ k : ℝ) : ℂ) := by
    rw [map_pow, ← mul_pow, Complex.mul_conj]
    exact (Complex.ofReal_pow (Complex.normSq z) k).symm
  rw [h1, Complex.ofReal_re, Complex.normSq_eq_norm_sq, ← pow_mul]

end Work.A3
