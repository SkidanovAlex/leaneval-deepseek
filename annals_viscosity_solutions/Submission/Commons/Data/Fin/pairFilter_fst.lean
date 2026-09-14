import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Fin

namespace Commons.Data.Fin

open scoped BigOperators
set_option autoImplicit false

lemma pairFilter_fst {N : ℕ} {α : Type*} [AddCommMonoid α] (k : Fin N) (f : Fin N → Fin N → α) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).filter
      (fun p => p.1 = k), f p.1 p.2) = ∑ j ∈ Finset.Ioi k, f k j := by
  classical
  -- Combine the two filters: first coordinate equals `k` and is less than the second.
  rw [Finset.filter_filter]
  -- Rewrite the (pair) filter sum as a double sum with an indicator.
  rw [Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  -- Collapse the inner sum over `j`: when `i = k` it is the sum over `j > k`,
  -- otherwise it vanishes.
  have h_inner : ∀ i : Fin N,
      (∑ j : Fin N, (if i < j ∧ i = k then f i j else 0)) =
        if i = k then (∑ j : Fin N, if i < j then f k j else 0) else 0 := by
    intro i
    by_cases hik : i = k
    · subst i
      simp
    · simp [hik]
  simp_rw [h_inner]
  -- Collapse the outer sum over `i` at the single index `i = k`.
  simp
  -- The remaining sum over `{j | k < j}` is precisely the sum over `Finset.Ioi k`.
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

end Commons.Data.Fin