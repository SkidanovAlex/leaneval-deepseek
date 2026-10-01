import Mathlib
import Submission.Work.LinnikAreas.Density4.vonMangoldt_sq_sum_bound
import Submission.Work.LinnikAreas.Density4.primes_sq_sum_lower

namespace Work.LinnikAreas.Density4

open scoped BigOperators

/-- The second moment of `Λ` up to `N` dominates the sum of `(log p)²` over primes `p ≤ N`:
every prime `p ≤ N` lies in `[1, N]` and there `Λ p = log p`, all terms being non-negative. -/
lemma primesLE_sq_sum_le_vonMangoldt_sq_sum (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, (Real.log (p : ℝ)) ^ 2)
      ≤ ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2 := by
  have hsub : Nat.primesLE N ⊆ Finset.Icc 1 N := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    exact Finset.mem_Icc.mpr ⟨le_trans (by norm_num : (1:ℕ) ≤ 2) hp.2.two_le, hp.1⟩
  have hcongr : (∑ p ∈ Nat.primesLE N, (Real.log (p : ℝ)) ^ 2)
      = ∑ p ∈ Nat.primesLE N, (ArithmeticFunction.vonMangoldt p) ^ 2 := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Nat.mem_primesLE] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
  rw [hcongr]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)

theorem vonMangoldt_sq_sum_lower : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    (N : ℝ) * Real.log (N : ℝ) - C * (N : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := primes_sq_sum_lower
  refine ⟨C₀, hC₀pos, ?_⟩
  intro N hN
  rcases eq_or_lt_of_le hN with h | h
  · -- `N = 1`: the sum is `Λ 1 ^ 2 = 0`, the left side is `-C₀ ≤ 0`.
    subst h
    have hsum : (∑ n ∈ Finset.Icc 1 1, (ArithmeticFunction.vonMangoldt n) ^ 2) = 0 := by
      simp [ArithmeticFunction.vonMangoldt_apply_one]
    rw [hsum]
    simp
    linarith [hC₀pos]
  · -- `N ≥ 2`: chain the prime lower bound with the reduction to all `n ≤ N`.
    have hN2 : 2 ≤ N := by omega
    exact (hC₀ N hN2).trans (primesLE_sq_sum_le_vonMangoldt_sq_sum N)

end Work.LinnikAreas.Density4
