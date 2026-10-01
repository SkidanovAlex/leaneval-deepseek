import Mathlib

namespace Work.ZeroFreeTables.P3

/-- Elementary dyadic/rational comparison used in the Heath–Brown zero-free
region argument.  Writing `x = 2^k * R`, the left-hand side is `2 * x / x ^ n`
and, since `x ≥ 1` and `n ≥ 2`, this is at most `2 * x / x ^ 2 = 2 / x`, which
is exactly the right-hand side.

The only inputs are `n ≥ 2` and `R ≥ 2` (which forces `x ≥ 1`). -/
theorem dyadicTermLe (n : ℕ) (hn : 2 ≤ n) {R : ℝ} (hR : 2 ≤ R) (k : ℕ) :
    (2 : ℝ) ^ (k + 1) * R / ((2 : ℝ) ^ k * R) ^ n ≤ 2 * (1 / 2 : ℝ) ^ k / R := by
  -- `x = 2^k * R` is at least `1`, hence so are all its powers.
  have hx1 : (1 : ℝ) ≤ (2 : ℝ) ^ k * R :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (by linarith)
  have hpow : ((2 : ℝ) ^ k * R) ^ 2 ≤ ((2 : ℝ) ^ k * R) ^ n :=
    pow_le_pow_right₀ hx1 hn
  -- numerator `2^(k+1) * R = 2 * x`
  have hnum : (2 : ℝ) ^ (k + 1) * R = 2 * ((2 : ℝ) ^ k * R) := by
    rw [pow_succ]; ring
  -- right-hand side `2 * (1/2)^k / R = 2 / x`
  have hRHS : 2 * (1 / 2 : ℝ) ^ k / R = 2 / ((2 : ℝ) ^ k * R) := by
    rw [one_div, inv_pow]
    field_simp
  rw [hnum, hRHS]
  calc 2 * ((2 : ℝ) ^ k * R) / ((2 : ℝ) ^ k * R) ^ n
      ≤ 2 * ((2 : ℝ) ^ k * R) / ((2 : ℝ) ^ k * R) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = 2 / ((2 : ℝ) ^ k * R) := by
        field_simp

end Work.ZeroFreeTables.P3
