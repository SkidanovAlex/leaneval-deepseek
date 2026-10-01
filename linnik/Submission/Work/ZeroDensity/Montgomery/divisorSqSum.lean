import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.ZeroDensity.Montgomery.divisorsCardDivSum_le
import Submission.Work.ZeroDensity.Montgomery.twoPowOmegaDivSum_le
import Submission.Work.ZeroDensity.Montgomery.cardDivisorsSq_eq_sum
import Submission.Work.ZeroDensity.Montgomery.logPowFour_le
import Submission.Work.ZeroDensity.Montgomery.sumDivisorsRecip_eq

/-!
# The second moment of the divisor function, with a `log⁴` saving

We prove `∑_{n ≤ N} τ(n)² / n ≤ C (log (2N))⁴` with an absolute constant `C`.

The proof uses the classical identity `τ = τ(·²) * 1` in the form
`τ(n)² = ∑_{d ∣ n} 2^{ω(d)} τ(n/d)`, the Dirichlet reindexing
`∑_{n ≤ N} n⁻¹ ∑_{d ∣ n} a_d b_{n/d} = ∑_{d ≤ N} (a_d/d) ∑_{m ≤ N/d} b_m/m`,
and the two elementary estimates
`∑_{m ≤ M} τ(m)/m ≤ (1 + log M)²` and `∑_{m ≤ M} 2^{ω(m)}/m ≤ (1 + log M)²`.
-/

open Finset

namespace Work.ZeroDensity.Montgomery

theorem divisorSqSum : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ)
      ≤ C * (Real.log (2 * (N : ℝ))) ^ 4 := by
  refine ⟨16, by norm_num, ?_⟩
  intro N hN
  -- replace `Icc 1 N` by `Ioc 0 N`
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc]
  -- expand the pointwise square of `τ` as a Dirichlet convolution
  have hstep2 : ∑ n ∈ Finset.Ioc 0 N, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ)
      = ∑ n ∈ Finset.Ioc 0 N, (1 / (n : ℝ)) *
          ∑ d ∈ n.divisors, (2 : ℝ) ^ (d.primeFactors.card) * (((n / d).divisors.card : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [cardDivisorsSq_eq_sum n, div_eq_inv_mul, one_div]
  rw [hstep2, sumDivisorsRecip_eq N (fun d => (2 : ℝ) ^ (d.primeFactors.card))
        (fun m => ((m.divisors.card : ℝ)))]
  -- bound the inner sum uniformly
  refine le_trans ?_ (logPowFour_le N hN)
  have hinner : ∀ d ∈ Finset.Ioc 0 N,
      ∑ m ∈ Finset.Ioc 0 (N / d), ((m.divisors.card : ℝ) / (m : ℝ))
        ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    obtain ⟨hd0, hdle⟩ := hd
    have h1 : 1 ≤ N / d := (Nat.one_le_div_iff hd0).mpr hdle
    have h2 : N / d ≤ N := Nat.div_le_self N d
    have h3 : Real.log (((N / d) : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast h2)
    have hlog1 : 0 ≤ Real.log (((N / d) : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast h1)
    have h4 : (1 + Real.log (((N / d) : ℕ) : ℝ)) ^ 2 ≤ (1 + Real.log (N : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    exact (divisorsCardDivSum_le (N / d)).trans h4
  calc ∑ d ∈ Finset.Ioc 0 N,
          (2 ^ d.primeFactors.card / (d : ℝ)) *
            ∑ m ∈ Finset.Ioc 0 (N / d), ((m.divisors.card : ℝ) / (m : ℝ))
      ≤ ∑ d ∈ Finset.Ioc 0 N,
          (2 ^ d.primeFactors.card / (d : ℝ)) * (1 + Real.log (N : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hinner d hd) (by positivity)
    _ = (1 + Real.log (N : ℝ)) ^ 2 *
          ∑ d ∈ Finset.Ioc 0 N, (2 ^ d.primeFactors.card / (d : ℝ)) := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 * (1 + Real.log (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left (twoPowOmegaDivSum_le N) (by positivity)
    _ = (1 + Real.log (N : ℝ)) ^ 4 := by ring

end Work.ZeroDensity.Montgomery
