import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.relChains_diagonal_injective

/-!
# The union of two `GoodV` pieces is `GoodV`

`Work.Compact.Noncompact.GoodV k X A` is the vanishing half of Hatcher's Lemma 3.27: `A` is
compact and `H_j(X, X∖A) = 0` for all `j > k+1`.

This file proves that the class of such `A` is closed under unions: if `A`, `B` and `A ∩ B` are
`GoodV`, then so is `A ∪ B`.  Passing to complements `U = Aᶜ`, `V = Bᶜ` (open, since a compact
subset of a Hausdorff space is closed), the relative Mayer–Vietoris sequence

`H_{j+1}(X, U∪V) ⟶ H_{j+1}(X,U) ⊕ H_{j+1}(X,V) ⟶ H_{j+1}(X, U∩V) ⟶ H_j(X, U∩V) ⟶ H_j(X,U) ⊕ H_j(X,V)`

says exactly that the diagonal `H_j(X, U∩V) ⟶ H_j(X,U) ⊕ H_j(X,V)` is injective because
`H_{j+1}(X, U∪V) = H_{j+1}(X, X∖(A∩B)) = 0`; that injectivity is the content of
`Work.Compact.Noncompact.relChains_diagonal_injective`.  Since `H_j(X,U) = H_j(X,V) = 0` for
`j > k+1`, the source `H_j(X, U∩V) = H_j(X, X∖(A∪B))` must vanish as well.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Compact.Noncompact

theorem goodV_union {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] (A B : Set M)
    (hA : GoodV k (TopCat.of M) A) (hB : GoodV k (TopCat.of M) B)
    (hAB : GoodV k (TopCat.of M) (A ∩ B)) : GoodV k (TopCat.of M) (A ∪ B) := by
  obtain ⟨hAc, hAv⟩ := hA
  obtain ⟨hBc, hBv⟩ := hB
  obtain ⟨_hABc, hABv⟩ := hAB
  refine ⟨hAc.union hBc, ?_⟩
  intro j hj
  -- write `j = m + 1`; then `H_j(X, X∖(A∪B)) ↪ H_j(X, X∖A) ⊕ H_j(X, X∖B)` by Mayer–Vietoris.
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  show IsZero ((Work.Cohomology.relChains (TopCat.of M) ((A ∪ B)ᶜ)).homology (m + 1))
  rw [Set.compl_union]
  -- the Mayer–Vietoris input: `H_{j+1}(X, X∖(A∩B)) = 0`.
  have hAB' : IsZero ((Work.Cohomology.relChains (TopCat.of M) ((A ∩ B)ᶜ)).homology (m + 2)) :=
    hABv (m + 2) (by omega)
  rw [Set.compl_inter] at hAB'
  -- compact subsets of a Hausdorff space are closed, so their complements are open.
  have hinj := relChains_diagonal_injective (X := TopCat.of M) (Aᶜ) (Bᶜ)
    hAc.isClosed.isOpen_compl hBc.isClosed.isOpen_compl m hAB'
  have s1 := (ModuleCat.isZero_iff_subsingleton).1 (hAv (m + 1) (by omega))
  have s2 := (ModuleCat.isZero_iff_subsingleton).1 (hBv (m + 1) (by omega))
  -- an injective map into a subsingleton (here `0 ⊕ 0`) has subsingleton source
  refine (ModuleCat.isZero_iff_subsingleton).2 ⟨fun x y => hinj ?_⟩
  exact Prod.ext (s1.allEq _ _) (s2.allEq _ _)

end Work.Compact.Noncompact
