import Mathlib
import Submission.Work.ZeroFreeTables.P9.tsum_sq_mul_geometric_le
import Submission.Work.ZeroFreeTables.P9.summable_vonMangoldt_primePow
import Submission.Work.ZeroFreeTables.P9.vonMangoldt_compl_coprime_eq_sum_F
import Submission.Work.ZeroFreeTables.P9.vonMangoldt_primePow_series_le

open scoped BigOperators

namespace Work.ZeroFreeTables.P9

/-- The `n`-th summand of the von Mangoldt tail attached to a single prime `p`
(and to a fixed real `σ` and exponent `j`): it is nonzero exactly on the powers
`p ^ k` (with `k ≥ 1`), where it equals `Λ (p ^ k) · (p ^ k) ^ (-σ) · (log (p ^ k)) ^ j`. -/
noncomputable def primePowTerm (σ : ℝ) (j : ℕ) (p n : ℕ) : ℝ :=
  if IsPrimePow n ∧ n.minFac = p then
    (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j
  else 0

/-- **The complementary (`gcd(n,q) > 1`) von Mangoldt tail is `O(1)` in `q`.**
For `σ > 1` and `j ≤ 2`,
`∑_n [gcd(n,q) > 1] Λ(n) (log n)^j / n^σ ≤ 12 ∑_{p ∣ q} (log p)^{j+1} / p`.

The summand vanishes unless `n` is a prime power `p^k` with `p ∣ q`, so the series
splits over the finitely many primes `p ∣ q`; for a fixed prime `p` it equals
`(log p)^{j+1} ∑_{k≥1} k^j p^{-kσ} ≤ (log p)^{j+1} · 12 / p`, using `σ > 1`
(so `p^{-σ} ≤ 1/p ≤ 1/2`) and `∑_{k≥1} k^j x^k ≤ 12 x` for `j ≤ 2`, `x ≤ 1/2`. -/
theorem vonMangoldt_coprime_compl_tail_le {q : ℕ} [NeZero q] {σ : ℝ} (hσ : 1 < σ) (j : ℕ) (hj : j ≤ 2) :
    (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j)
      ≤ 12 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
  have hq : q ≠ 0 := NeZero.ne q
  -- Pointwise splitting: the single tail equals the sum over the primes `p ∣ q`
  -- of the prime-power tails.
  have hpoint : ∀ n : ℕ,
      (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j
        = ∑ p ∈ q.primeFactors, primePowTerm σ j p n := by
    intro n
    rw [vonMangoldt_compl_coprime_eq_sum_F hq j n]
    simp only [primePowTerm]
  calc (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j)
      = ∑' n : ℕ, ∑ p ∈ q.primeFactors, primePowTerm σ j p n := tsum_congr hpoint
    _ = ∑ p ∈ q.primeFactors, ∑' n : ℕ, primePowTerm σ j p n := by
        exact Summable.tsum_finsetSum
          (fun p hp => summable_vonMangoldt_primePow p (Nat.prime_of_mem_primeFactors hp) hσ j)
    _ ≤ ∑ p ∈ q.primeFactors, 12 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
        exact Finset.sum_le_sum
          (fun p hp => vonMangoldt_primePow_series_le p (Nat.prime_of_mem_primeFactors hp) hσ j hj)
    _ = 12 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
        rw [Finset.mul_sum]
        simp only [mul_div_assoc]

end Work.ZeroFreeTables.P9
