import Mathlib

namespace Work.A7

/-- For `M ≤ 3N`, `A ≥ 0`, `1 ≤ N` and `e + 2 ≤ d`, the quotient `A M^e / N^d` is bounded by
`A 3^e / N^2`: the growth of `M^e ≤ 3^e N^e` is absorbed by the extra two powers of `N`
available in the denominator. -/
theorem mul_pow_div_le_sq {N d e : ℕ} {A M : ℝ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ 3 * N)
    (hA : 0 ≤ A) (he : e + 2 ≤ d) :
    A * M ^ e / (N : ℝ) ^ d ≤ A * 3 ^ e / (N : ℝ) ^ 2 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hM0 : (0:ℝ) ≤ M := by linarith
  rw [div_le_div_iff₀ (pow_pos hN0 d) (pow_pos hN0 2)]
  have key : M ^ e * (N:ℝ) ^ 2 ≤ 3 ^ e * (N:ℝ) ^ d := by
    have h1 : M ^ e ≤ (3 * (N:ℝ)) ^ e := pow_le_pow_left₀ hM0 hM e
    have h3 : (N:ℝ) ^ (e+2) ≤ (N:ℝ) ^ d := pow_le_pow_right₀ hN1 he
    calc M ^ e * (N:ℝ)^2 ≤ (3 * (N:ℝ))^e * (N:ℝ)^2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 3^e * ((N:ℝ)^e * (N:ℝ)^2) := by rw [mul_pow]; ring
      _ = 3^e * (N:ℝ)^(e+2) := by rw [← pow_add]
      _ ≤ 3^e * (N:ℝ)^d := mul_le_mul_of_nonneg_left h3 (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left key hA]

end Work.A7
