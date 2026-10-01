import Mathlib

namespace Work.LinnikAreas.Density4

/-- The `p ^ i`-term of the Farey/first-factor sum: for a prime `p`,
`p ^ i * μ(p ^ i) ^ 2 / φ(p ^ i)` equals `1` for `i = 0`, `p / (p - 1)` for
`i = 1`, and `0` for `i ≥ 2`. -/
theorem faf_prime_pow (p i : ℕ) (hp : Nat.Prime p) :
    ((p : ℝ) ^ i) * (((ArithmeticFunction.moebius (p ^ i) : ℤ) : ℝ)) ^ 2 / (Nat.totient (p ^ i) : ℝ)
      = if i = 0 then 1 else if i = 1 then (p : ℝ) / ((p : ℝ) - 1) else 0 := by
  by_cases hi0 : i = 0
  · simp [hi0]
  by_cases hi1 : i = 1
  · subst hi1
    simp only [pow_one]
    rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
    push_cast
    rw [Nat.cast_sub hp.one_le]
    norm_num
  · have hmu : ArithmeticFunction.moebius (p ^ i) = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp hi0, if_neg hi1]
    simp only [hmu, Int.cast_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_div,
      if_neg hi0, if_neg hi1]

end Work.LinnikAreas.Density4
