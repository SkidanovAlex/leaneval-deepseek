import Mathlib.Data.Fintype.BigOperators
import Submission.Work.BoseBoxFock.pairSet_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem sum_univ_eq_diag_add_pairSet {N : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Fin N × Fin N → M) :
    (∑ i : Fin N, ∑ j : Fin N, f (i, j))
      = (∑ i : Fin N, f (i, i)) + ∑ p ∈ Submission.BoseGases.pairSet N, f p := by
  -- `pairSet N` is the off-diagonal of `univ : Finset (Fin N)`.
  rw [pairSet_eq_univ_offDiag]
  -- the double sum over `Fin N × Fin N` is the sum over the product type
  rw [← Fintype.sum_prod_type]
  -- split the full square into its diagonal and its off-diagonal
  have hU : (Finset.univ : Finset (Fin N × Fin N))
      = (Finset.univ : Finset (Fin N)).diag ∪ (Finset.univ : Finset (Fin N)).offDiag := by
    rw [Finset.diag_union_offDiag, Finset.univ_product_univ]
  rw [hU, Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  congr 1
  -- the diagonal sum is `∑ i, f (i, i)`
  rw [Finset.diag, Finset.sum_map]
  simp

end Work.BoseBoxFock
