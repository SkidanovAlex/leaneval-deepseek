import Mathlib

namespace Work.FIArea6Hecke.R

/-- The sum of the logarithms of a set of distinct primes dividing `4 * d` is at most
`log (4 * d)`, since the product of those primes divides `4 * d`. -/
lemma sum_log_primes_le (d : ℕ) (S : Finset ℕ) (hd : 1 ≤ d)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d) :
    ∑ p ∈ S, Real.log p ≤ Real.log (4 * (d : ℝ)) := by
  have hne : 4 * d ≠ 0 := by omega
  -- every element of `S` is a prime factor of `4 * d`
  have hsub : S ⊆ (4 * d).primeFactors := by
    intro p hp
    exact Nat.Prime.mem_primeFactors (hS p hp).1 (hS p hp).2 hne
  calc ∑ p ∈ S, Real.log p
      ≤ ∑ p ∈ (4 * d).primeFactors, Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i _ _
        exact Real.log_natCast_nonneg i
    _ = Real.log (∏ p ∈ (4 * d).primeFactors, (p : ℝ)) := by
        rw [Real.log_prod]
        intro p hp
        exact Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero
    _ = Real.log ((∏ p ∈ (4 * d).primeFactors, p : ℕ) : ℝ) := by
        rw [Nat.cast_prod]
    _ ≤ Real.log ((4 * d : ℕ) : ℝ) := by
        apply Real.log_le_log
        · have hprod : 0 < ∏ p ∈ (4 * d).primeFactors, p :=
            Finset.prod_pos fun p hp => (Nat.mem_primeFactors.mp hp).1.pos
          exact_mod_cast hprod
        · exact_mod_cast
            (Nat.le_of_dvd (by omega : 0 < 4 * d) (Nat.prod_primeFactors_dvd (4 * d)))
    _ = Real.log (4 * (d : ℝ)) := by
        congr 1
        push_cast
        ring

end Work.FIArea6Hecke.R
