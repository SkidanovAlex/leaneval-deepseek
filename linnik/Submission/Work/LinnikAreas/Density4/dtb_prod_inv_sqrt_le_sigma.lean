import Mathlib

namespace Work.LinnikAreas.Density4

/-- For any finite set `t` of naturals, the reciprocal square root of the product of `t`
equals the product of the reciprocal square roots of the elements of `t`. -/
lemma one_div_sqrt_finset_prod (t : Finset ℕ) :
    (1 : ℝ) / Real.sqrt ((t.val.prod : ℕ) : ℝ) = ∏ p ∈ t, (1 : ℝ) / Real.sqrt (p : ℝ) := by
  have hcast : ((t.val.prod : ℕ) : ℝ) = ∏ p ∈ t, (p : ℝ) := by
    rw [Nat.cast_multiset_prod, ← Finset.prod_eq_multiset_prod]
  rw [hcast, Real.sqrt_prod t (fun p _ => Nat.cast_nonneg p), Finset.prod_div_distrib]
  simp

/-- The product over the prime factors `p` of `r` of `1 + 1/√p` is at most the sum over all
divisors `d` of `r` of `1/√d`. -/
theorem dtb_prod_inv_sqrt_le_sigma (r : ℕ) (hr : 1 ≤ r) :
    (∏ p ∈ r.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
      ≤ ∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ) := by
  have hr0 : r ≠ 0 := by omega
  -- expand the product into a sum over the powerset of the prime factors
  rw [Finset.prod_one_add (f := fun p : ℕ => (1 : ℝ) / Real.sqrt (p : ℝ)) r.primeFactors]
  have hF : (UniqueFactorizationMonoid.normalizedFactors r).toFinset = r.primeFactors := by
    rw [UniqueFactorizationMonoid.toFinset_normalizedFactors]
    exact congrFun UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors r
  -- identify the squarefree-divisor sum with the powerset sum
  have hsq : (∑ d ∈ r.divisors with Squarefree d, (1 : ℝ) / Real.sqrt (d : ℝ))
      = ∑ t ∈ r.primeFactors.powerset, ∏ p ∈ t, (1 : ℝ) / Real.sqrt (p : ℝ) := by
    rw [Nat.sum_divisors_filter_squarefree (f := fun d : ℕ => (1 : ℝ) / Real.sqrt (d : ℝ)) hr0,
      hF]
    exact Finset.sum_congr rfl (fun t _ => one_div_sqrt_finset_prod t)
  rw [← hsq]
  -- enlarge the sum from squarefree divisors to all divisors
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun d _ _ => by positivity)

end Work.LinnikAreas.Density4
