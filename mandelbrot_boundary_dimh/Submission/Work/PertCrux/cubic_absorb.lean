import Mathlib

namespace Work.PertCrux

/-- Absorption step: the linear-logarithmic bound `M ≤ 100 N (2 + log (4N))` is
dominated by `10 ^ 6 * S ^ 3 + 10 ^ 6` as soon as `N ≥ 65` and `S ≥ N`.

Indeed `log (4N) ≤ 4N`, so `M ≤ 200 N + 400 N ^ 2 ≤ 10 ^ 6 * N ^ 3 ≤ 10 ^ 6 * S ^ 3`. -/
theorem cubic_absorb {M N S : ℝ} (hN : 65 ≤ N) (hS : N ≤ S)
    (hM : M ≤ 100 * N * (2 + Real.log (4 * N))) :
    M ≤ 10 ^ 6 * S ^ 3 + 10 ^ 6 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have h4N : (0 : ℝ) < 4 * N := by linarith
  have hlog : Real.log (4 * N) ≤ 4 * N := by
    have h := Real.log_le_sub_one_of_pos h4N
    linarith
  have h1 : M ≤ 200 * N + 400 * N ^ 2 := by
    have h2 : 100 * N * (2 + Real.log (4 * N)) ≤ 100 * N * (2 + 4 * N) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ 100 * N)
      linarith
    nlinarith [h2]
  have h2 : 200 * N + 400 * N ^ 2 ≤ 10 ^ 6 * N ^ 3 := by nlinarith
  have h3 : N ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ (by linarith) hS 3
  nlinarith [h1, h2, h3]

end Work.PertCrux
