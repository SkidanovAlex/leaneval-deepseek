import Mathlib

namespace Work.LinnikAreas.Density4

/-- Splitting a product over the primes below `N` according to membership in `r.primeFactors`,
    valid when all prime factors of `r` are among the primes below `N`. -/
theorem prod_primesBelow_split (r N : ℕ) (hN : r.primeFactors ⊆ Nat.primesBelow N) (f : ℕ → ℝ) :
    (∏ p ∈ Nat.primesBelow N, f p)
      = (∏ p ∈ Nat.primesBelow N, (if p ∈ r.primeFactors then 1 else f p))
        * (∏ p ∈ r.primeFactors, f p) := by
  rw [Finset.prod_ite (f := fun _ => (1 : ℝ)) (g := f)]
  simp only [Finset.prod_const_one, one_mul]
  rw [← Finset.sdiff_eq_filter]
  exact (Finset.prod_sdiff hN).symm

end Work.LinnikAreas.Density4
