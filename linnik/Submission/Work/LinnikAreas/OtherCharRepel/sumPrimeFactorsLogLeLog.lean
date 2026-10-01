import Mathlib

namespace Work.LinnikAreas.OtherCharRepel

/-- The sum of the logarithms of the prime divisors of a nonzero natural number is at most the
logarithm of that number. -/
theorem sumPrimeFactorsLogLeLog (n : ℕ) (hn : n ≠ 0) :
    ∑ p ∈ n.primeFactors, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  have hpos : ∀ p ∈ n.primeFactors, (0 : ℝ) < (p : ℝ) := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hlog : Real.log (∏ p ∈ n.primeFactors, (p : ℝ))
      = ∑ p ∈ n.primeFactors, Real.log (p : ℝ) :=
    Real.log_prod (fun p hp => ne_of_gt (hpos p hp))
  rw [← hlog]
  apply Real.log_le_log
  · exact Finset.prod_pos hpos
  · have hle : (∏ p ∈ n.primeFactors, p : ℕ) ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
    calc ∏ p ∈ n.primeFactors, (p : ℝ)
        = ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) :=
          (Nat.cast_prod (fun p => p) n.primeFactors).symm
      _ ≤ (n : ℝ) := by exact_mod_cast hle

end Work.LinnikAreas.OtherCharRepel
