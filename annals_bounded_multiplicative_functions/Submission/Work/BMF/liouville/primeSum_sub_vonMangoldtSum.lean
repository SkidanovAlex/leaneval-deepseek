import Mathlib
import Submission.Commons.Analysis.Series.summable_log_div_sq_and_tsum_le_one
import Submission.Work.BMF.liouville.weighted_vonMangoldt_decomp
import Submission.Work.BMF.liouville.primesLE_sum_log_div_mul_pred_le_two
import Submission.Work.BMF.liouville.norm_row_tail_prime_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open ArithmeticFunction

/-- Splitting off the `k = 1` term of `Icc 1 K` (the case `K = 0` is excluded, since then
`1 ∉ Icc 1 K`). -/
private lemma sum_Icc_one_sub_singleton (f : ℕ → ℂ) {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.Icc 1 K, f k) - f 1 = ∑ k ∈ Finset.Icc 2 K, f k := by
  have hsub : ({1} : Finset ℕ) ⊆ Finset.Icc 1 K := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_Icc.mpr ⟨le_rfl, hK⟩
  have hset : (Finset.Icc 1 K) \ {1} = Finset.Icc 2 K := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
    omega
  calc (∑ k ∈ Finset.Icc 1 K, f k) - f 1
      = (∑ k ∈ Finset.Icc 1 K \ {1}, f k + ∑ k ∈ ({1} : Finset ℕ), f k) - f 1 := by
        rw [← Finset.sum_sdiff hsub]
    _ = (∑ k ∈ Finset.Icc 1 K \ {1}, f k + f 1) - f 1 := by rw [Finset.sum_singleton]
    _ = ∑ k ∈ Finset.Icc 1 K \ {1}, f k := by ring
    _ = ∑ k ∈ Finset.Icc 2 K, f k := by rw [hset]

/-- Splitting off the `k = 1` term of `Icc 1 K`, in the sign convention used below. -/
private lemma one_sub_sum_Icc_eq (f : ℕ → ℂ) {K : ℕ} (hK : 1 ≤ K) :
    f 1 - (∑ k ∈ Finset.Icc 1 K, f k) = -(∑ k ∈ Finset.Icc 2 K, f k) := by
  rw [← sum_Icc_one_sub_singleton f hK]
  ring

/-- The prime sum `∑_{p ≤ M} f p · log p / p` minus the full prime-power sum
`∑_{p ≤ M} ∑_{k ≤ log_p M} f(p^k) · log p / p^k` is minus the `k ≥ 2` part. -/
private lemma primeSum_sub_primePowerSum_eq_neg_tail (f : ℕ → ℂ) (M : ℕ) :
    (∑ p ∈ M.primesLE, f p * (Real.log (p:ℝ) : ℂ) / (p:ℂ))
      - (∑ p ∈ M.primesLE, ∑ k ∈ Finset.Icc 1 (Nat.log p M),
            f (p^k) * (Real.log (p:ℝ) : ℂ) / ((p:ℂ)^k))
      = -(∑ p ∈ M.primesLE, ∑ k ∈ Finset.Icc 2 (Nat.log p M),
            f (p^k) * (Real.log (p:ℝ) : ℂ) / ((p:ℂ)^k)) := by
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hK : 1 ≤ Nat.log p M :=
    Nat.le_log_of_pow_le (Nat.prime_of_mem_primesLE hp).one_lt
      (by simpa using Nat.le_of_mem_primesLE hp)
  simpa using one_sub_sum_Icc_eq (fun k => f (p^k) * (Real.log (p:ℝ) : ℂ) / ((p:ℂ)^k)) hK

/-- For any Dirichlet character `ψ` of level `d` and any `M`, the prime sum `∑_{p ≤ M} ψ(p)·log p / p`
differs from the von Mangoldt sum `∑_{n ≤ M} ψ(n)·Λ(n) / n` by at most an absolute constant `2`.

Indeed the difference is the `k ≥ 2` part `∑_{p^k ≤ M, k ≥ 2} ψ(p)^k log p / p^k`, whose norm is
`≤ ∑_p log p/(p(p-1)) ≤ 2 ∑_p log p/p² ≤ 2 ∑_n log n/n² ≤ 2` (last step:
`Commons.Analysis.Series.summable_log_div_sq_and_tsum_le_one`).

For the identity, the decomposition of `∑_{n ≤ M} Λ n` into prime powers in
`Chebyshev.psi_eq_sum_mul_log_prime` (`Mathlib.NumberTheory.Chebyshev`) can be copied verbatim,
replacing `Λ m` by `ψ m * Λ m / m`: use `Nat.primesLE_eq_filter_Icc_one`, `Finset.sum_biUnion`,
`Finset.sum_image` with `Nat.pow_right_injective`, `ArithmeticFunction.vonMangoldt_apply_pow`,
`vonMangoldt_apply_prime`, `vonMangoldt_eq_zero_iff`, and `map_pow`. -/
theorem primeSum_sub_vonMangoldtSum (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (M : ℕ) :
    ‖(∑ p ∈ M.primesLE, ψ p * ((Real.log (p:ℝ) : ℂ) / (p : ℂ)))
      - (∑ n ∈ Finset.Icc 1 M, ψ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ))‖ ≤ 2 := by
  -- The von Mangoldt sum is the full prime-power sum (`k ≥ 1`).
  have hB : (∑ n ∈ Finset.Icc 1 M, ψ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ))
      = ∑ p ∈ M.primesLE, ∑ k ∈ Finset.Icc 1 (Nat.log p M),
          ψ (p ^ k) * (Real.log (p:ℝ) : ℂ) / ((p:ℂ)^k) := by
    have h := weighted_vonMangoldt_decomp (fun n : ℕ => ψ n) M
    simpa using h
  -- The prime sum is the `k = 1` part of the same sum.
  have hA : (∑ p ∈ M.primesLE, ψ p * ((Real.log (p:ℝ) : ℂ) / (p : ℂ)))
      = ∑ p ∈ M.primesLE, ψ p * (Real.log (p:ℝ) : ℂ) / (p : ℂ) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [mul_div_assoc]
  -- Hence the difference is (minus) the `k ≥ 2` tail.
  have hdiff : (∑ p ∈ M.primesLE, ψ p * ((Real.log (p:ℝ) : ℂ) / (p : ℂ)))
      - (∑ n ∈ Finset.Icc 1 M, ψ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ))
      = -(∑ p ∈ M.primesLE, ∑ k ∈ Finset.Icc 2 (Nat.log p M),
          ψ (p^k) * (Real.log (p:ℝ) : ℂ) / ((p:ℂ)^k)) := by
    rw [hA, hB]
    simpa only [Nat.cast_pow] using primeSum_sub_primePowerSum_eq_neg_tail (fun n : ℕ => ψ n) M
  rw [hdiff, norm_neg]
  -- Bound the tail: one row at a time, then the geometric/`ζ(2)`-type estimate.
  refine le_trans (norm_sum_le M.primesLE _) ?_
  refine le_trans (Finset.sum_le_sum ?_) (primesLE_sum_log_div_mul_pred_le_two M)
  intro p hp
  exact norm_row_tail_prime_le d ψ p (Nat.log p M) (Nat.prime_of_mem_primesLE hp)

end Work.BMF.liouville
