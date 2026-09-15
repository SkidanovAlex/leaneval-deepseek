import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Commons.Algebra.BigOperators

/-- Multilinear expansion of a product of `(g i - c)` over a finite index set:
`∏ i, (g i - c) = ∑_{S} (-c)^(n - |S|) * ∏_{i ∈ S} g i`. -/
theorem prod_sub_const_expand {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (g : ι → R) (c : R) :
    ∏ i, (g i - c) = ∑ S : Finset ι, (-c) ^ (Fintype.card ι - S.card) * ∏ i ∈ S, g i := by
  classical
  -- Rewrite each factor as `g i + (-c)` and expand the product of sums over the powerset.
  have h : ∏ i, (g i - c) = ∏ i, (g i + (-c)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sub_eq_add_neg]
  rw [h, Fintype.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_const, Finset.card_compl, mul_comm]

end Commons.Algebra.BigOperators