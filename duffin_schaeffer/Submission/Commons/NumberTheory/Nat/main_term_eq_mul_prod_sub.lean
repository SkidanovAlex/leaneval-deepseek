import Mathlib

open scoped BigOperators

namespace Commons.NumberTheory.Nat

/-- The product over a finite set of reciprocals of naturals equals the reciprocal of
the product (in a field, where `0⁻¹ = 0`). -/
lemma prod_one_div_eq_inv_prod (S : Finset ℕ) :
    (∏ p ∈ S, ((1 : ℝ) / (p : ℝ))) = (∏ p ∈ S, (p : ℝ))⁻¹ := by
  calc
    (∏ p ∈ S, ((1 : ℝ) / (p : ℝ))) = ∏ p ∈ S, ((p : ℝ)⁻¹) := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      simp [one_div]
    _ = (∏ p ∈ S, (p : ℝ))⁻¹ := by
      exact Finset.prod_inv_distrib (s := S) (f := fun p : ℕ => (p : ℝ))

/-- Inclusion-exclusion over the prime factors of `q`:
`∑_{S ⊆ primeFactors q} (-1)^{|S|} L / ∏_{p ∈ S} p = L * ∏_{p | q, p prime} (1 - 1/p)`. -/
theorem main_term_eq_mul_prod_sub (q L : ℕ) :
    (∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * ((L : ℝ) / ∏ p ∈ S, (p : ℝ))) =
      (L : ℝ) * ∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  classical
  -- Expansion of the product `∏_p (1 - 1/p)` into a sum over subsets `S`.
  have hprod : (∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ))) =
      ∑ S ∈ q.primeFactors.powerset, (-1 : ℝ) ^ S.card * ∏ p ∈ S, ((1 : ℝ) / (p : ℝ)) := by
    simpa [Finset.prod_const_one] using
      (Finset.prod_sub (R := ℝ) (s := q.primeFactors) (f := fun _ : ℕ => (1 : ℝ))
        (g := fun p : ℕ => (1 : ℝ) / (p : ℝ)))
  calc
    (∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * ((L : ℝ) / ∏ p ∈ S, (p : ℝ)))
        = ∑ S ∈ q.primeFactors.powerset,
            (L : ℝ) * ((-1 : ℝ) ^ S.card * ∏ p ∈ S, ((1 : ℝ) / (p : ℝ))) := by
          apply Finset.sum_congr rfl
          intro S hS
          calc
            (-1 : ℝ) ^ S.card * ((L : ℝ) / ∏ p ∈ S, (p : ℝ))
                = (-1 : ℝ) ^ S.card * ((L : ℝ) * (∏ p ∈ S, (p : ℝ))⁻¹) := by
                  rw [div_eq_mul_inv]
            _ = (-1 : ℝ) ^ S.card * ((L : ℝ) * (∏ p ∈ S, ((1 : ℝ) / (p : ℝ)))) := by
                  rw [prod_one_div_eq_inv_prod S]
            _ = (L : ℝ) * ((-1 : ℝ) ^ S.card * (∏ p ∈ S, ((1 : ℝ) / (p : ℝ)))) := by ring
    _ = (L : ℝ) * (∑ S ∈ q.primeFactors.powerset,
            (-1 : ℝ) ^ S.card * ∏ p ∈ S, ((1 : ℝ) / (p : ℝ))) := by
          rw [Finset.mul_sum]
    _ = (L : ℝ) * ∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
          rw [hprod]

end Commons.NumberTheory.Nat
