import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

namespace Commons.Algebra.Ring

open scoped BigOperators

set_option autoImplicit false

/-- **Corrected form of the paper's `sum of sq adj op` lemma.**  If, for every `e ∈ E`,
`adj e` and `op e` are disjoint subsets of `E.erase e` whose union covers
`E \ {e}` (i.e. they genuinely *partition* `E \ {e}`), then
`(∑_{e ∈ E} D e)² = ∑_{e ∈ E} (D e)² + ∑_{e ∈ E} D e·∑_{f ∈ adj e} D f + ∑_{e ∈ E} D e·∑_{f ∈ op e} D f`.
The extra hypothesis `adj e ⊆ E.erase e` (resp. `op e ⊆ E.erase e`), absent from
`Commons.Algebra.Ring.sq_sum_eq_sum_sq_add_adj_op`, is what makes the identity true. -/
theorem sq_sum_eq_sum_sq_add_partition {A ι : Type*} [Ring A] [DecidableEq ι]
    (E : Finset ι) (D : ι → A) (adj op : ι → Finset ι)
    (hadj : ∀ e ∈ E, adj e ⊆ E.erase e) (hop : ∀ e ∈ E, op e ⊆ E.erase e)
    (hdisj : ∀ e ∈ E, Disjoint (adj e) (op e))
    (hcover : ∀ e ∈ E, ∀ f ∈ E, f ≠ e → f ∈ adj e ∨ f ∈ op e) :
    (∑ e ∈ E, D e) ^ 2
      = (∑ e ∈ E, D e ^ 2) + (∑ e ∈ E, D e * ∑ f ∈ adj e, D f)
        + (∑ e ∈ E, D e * ∑ f ∈ op e, D f) := by
  -- The two sets `adj e` and `op e` partition `E.erase e`.
  have key : ∀ e ∈ E,
      ∑ f ∈ E.erase e, D f = (∑ f ∈ adj e, D f) + (∑ f ∈ op e, D f) := by
    intro e he
    have hEq : E.erase e = adj e ∪ op e := by
      apply Finset.Subset.antisymm
      · intro f hf
        rw [Finset.mem_union]
        rw [Finset.mem_erase] at hf
        exact hcover e he f hf.2 hf.1
      · exact Finset.union_subset (hadj e he) (hop e he)
    rw [hEq, Finset.sum_union (hdisj e he)]
  -- The inner sum over `E` decomposes for each `e ∈ E`.
  have hinner : ∀ e ∈ E,
      ∑ f ∈ E, D e * D f
        = D e ^ 2 + (D e * ∑ f ∈ adj e, D f) + (D e * ∑ f ∈ op e, D f) := by
    intro e he
    rw [← Finset.sum_erase_add E (fun f => D e * D f) he, ← Finset.mul_sum,
      key e he, mul_add, sq]
    abel
  -- Distribute the outer sum.
  have hsum :
      ∑ e ∈ E, (D e ^ 2 + (D e * ∑ f ∈ adj e, D f) + (D e * ∑ f ∈ op e, D f))
        = (∑ e ∈ E, D e ^ 2) + (∑ e ∈ E, D e * ∑ f ∈ adj e, D f)
          + (∑ e ∈ E, D e * ∑ f ∈ op e, D f) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [sq, Finset.sum_mul_sum,
    Finset.sum_congr rfl hinner, hsum]

end Commons.Algebra.Ring