import Mathlib

namespace Work.A7

/-- Elementary comparison: if `1 ≤ N`, `1 ≤ M ≤ 3N` and `e + 1 ≤ d`, then dividing
`A · M^e` by `N^d` is at most dividing `A · 3^e` by `N` (for `0 ≤ A`).

The point is that `M^e ≤ (3N)^e = 3^e N^e` while `N^e · N = N^{e+1} ≤ N^d`, so that
`M^e · N ≤ 3^e · N^d`; clearing denominators (`N^d, N > 0`) gives the claim. -/
theorem mul_pow_div_le {N d e : ℕ} {A M : ℝ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ 3 * N)
    (hA : 0 ≤ A) (he : e + 1 ≤ d) :
    A * M ^ e / (N : ℝ) ^ d ≤ A * 3 ^ e / (N : ℝ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  -- `M^e ≤ 3^e N^e`
  have h1 : M ^ e ≤ 3 ^ e * (N : ℝ) ^ e := by
    have := pow_le_pow_left₀ (le_of_lt hMpos) hM e
    simpa [mul_pow] using this
  -- `N^{e+1} ≤ N^d`
  have h2 : (N : ℝ) ^ (e + 1) ≤ (N : ℝ) ^ d := pow_le_pow_right₀ hN1 he
  -- the key cleared-denominator inequality
  have key : M ^ e * (N : ℝ) ≤ 3 ^ e * (N : ℝ) ^ d := by
    calc M ^ e * (N : ℝ) ≤ (3 ^ e * (N : ℝ) ^ e) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hNpos)
      _ = 3 ^ e * ((N : ℝ) ^ e * (N : ℝ)) := by ring
      _ = 3 ^ e * (N : ℝ) ^ (e + 1) := by rw [pow_succ]
      _ ≤ 3 ^ e * (N : ℝ) ^ d := mul_le_mul_of_nonneg_left h2 (by positivity)
  -- divide by `N^d` and `N` (both positive) to get the core inequality
  have hcore : M ^ e / (N : ℝ) ^ d ≤ 3 ^ e / (N : ℝ) := by
    rw [div_le_iff₀ (pow_pos hNpos d), div_mul_eq_mul_div, le_div_iff₀ hNpos]
    exact key
  calc A * M ^ e / (N : ℝ) ^ d = A * (M ^ e / (N : ℝ) ^ d) := by rw [mul_div_assoc]
    _ ≤ A * (3 ^ e / (N : ℝ)) := mul_le_mul_of_nonneg_left hcore hA
    _ = A * 3 ^ e / (N : ℝ) := by rw [mul_div_assoc]

end Work.A7
