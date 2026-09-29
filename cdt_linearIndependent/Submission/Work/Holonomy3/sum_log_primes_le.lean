import Mathlib
import Mathlib.NumberTheory.Chebyshev

namespace Work.Holonomy3

/-- Chebyshev's bound for a finite set of primes: if every `p ∈ S` is a prime with `p ≤ K`,
then `∑_{p ∈ S} log p ≤ log 4 · K`.  Indeed `S ⊆ primesLE K`, the sum over that set is `θ K`,
and Mathlib's Chebyshev estimate gives `θ x ≤ log 4 · x`. -/
theorem sum_log_primes_le {S : Finset ℕ} {K : ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≤ K) :
    ∑ p ∈ S, Real.log (p : ℝ) ≤ Real.log 4 * (K : ℝ) := by
  have hsub : S ⊆ Nat.primesLE K := by
    intro p hp
    obtain ⟨hpp, hpK⟩ := hS p hp
    exact Nat.mem_primesLE.mpr ⟨hpK, hpp⟩
  calc ∑ p ∈ S, Real.log (p : ℝ)
      ≤ ∑ p ∈ Nat.primesLE K, Real.log (p : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro x hxT _
        exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hxT).one_le)
    _ = Chebyshev.theta (K : ℝ) := (Chebyshev.theta_eq_sum_primesLE_log K).symm
    _ ≤ Real.log 4 * (K : ℝ) := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg K)

end Work.Holonomy3
