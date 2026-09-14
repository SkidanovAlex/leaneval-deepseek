import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Squarefree

namespace Commons.Data.Nat

open scoped BigOperators

/-- The product of the elements of a finite set of (distinct) primes is squarefree. -/
theorem squarefree_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  have hN : (∏ p ∈ s, p) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hs p hp).ne_zero)
  refine Nat.squarefree_of_factorization_le_one hN ?_
  intro p
  calc
    ((∏ x ∈ s, x).factorization) p = ∑ x ∈ s, x.factorization p := by
      exact Nat.factorization_prod_apply (S := s) (g := fun x : ℕ => x)
        (fun x hx => (hs x hx).ne_zero)
    _ = ∑ x ∈ s, if x = p then 1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hpx : x.factorization = Finsupp.single x 1 := (hs x hx).factorization
      by_cases h : x = p
      · subst h
        simp [hpx]
      · simp [hpx, h]
    _ = if p ∈ s then 1 else 0 := by
      rw [Finset.sum_ite_eq']
    _ ≤ 1 := by
      by_cases hp : p ∈ s <;> simp [hp]

end Commons.Data.Nat