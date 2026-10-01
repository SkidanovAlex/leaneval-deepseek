import Mathlib
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

namespace Work.ZeroFreeTables.P9

open ArithmeticFunction

/-- The restriction of the logarithmically weighted von Mangoldt series to prime powers
whose least prime factor is `p` is summable, for `σ > 1` and any `j : ℕ`.

Indeed the restricted summand is dominated by `Λ n * (log n)^j / n^σ`, whose summability
is `Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow`. -/
theorem summable_vonMangoldt_primePow (p : ℕ) (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) (j : ℕ) : Summable (fun n : ℕ => if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)) := by
  have hmaj : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log (n : ℝ)) ^ j / (n : ℝ) ^ σ) :=
    Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow hσ j
  refine Summable.of_norm_bounded hmaj ?_
  intro n
  by_cases h : IsPrimePow n ∧ n.minFac = p
  · have hn1 : 1 < n := IsPrimePow.one_lt h.1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hn1)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hrpow : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (le_of_lt hnpos) _
    rw [if_pos h, Real.norm_of_nonneg (mul_nonneg (mul_nonneg hΛ hrpow) (pow_nonneg hlog j)),
      Real.rpow_neg (le_of_lt hnpos) σ, div_eq_mul_inv]
    exact le_of_eq (by ring)
  · rw [if_neg h, norm_zero]
    exact div_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (pow_nonneg (Real.log_natCast_nonneg n) j))
      (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

end Work.ZeroFreeTables.P9
