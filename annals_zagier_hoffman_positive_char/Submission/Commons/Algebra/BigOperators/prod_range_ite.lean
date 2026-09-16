import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Nat

open Finset

namespace Commons.Algebra.BigOperators

/-- A product over `range N` of the "indicator-restricted" function `i ↦ if i < m then f i else 1`
is the product of `f` over `range (min m N)`. -/
lemma prod_range_ite {M : Type*} [CommMonoid M] (f : ℕ → M) (m N : ℕ) :
    (∏ i ∈ Finset.range N, (if i < m then f i else 1)) = ∏ i ∈ Finset.range (min m N), f i := by
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  tauto

end Commons.Algebra.BigOperators
