import Mathlib
import Submission.Work.Cohomology.sdHomotopy
import Submission.Work.Cohomology.PushChain
import Submission.Work.Cohomology.Mesh

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Iterates of the subdivision chain map

`Work.Cohomology.sdChainMap X : C_*(X) ⟶ C_*(X)` is the barycentric subdivision of singular chains
(`Submission/Work/Cohomology/sdChainMap.lean`), chain homotopic to the identity
(`Work.Cohomology.sdHomotopy`).  This file packages its iterates

`sdChainMapIter X N = sdChainMap X ≫ sdChainMap X ≫ ⋯ ≫ sdChainMap X`  (`N` factors)

and proves that every iterate is again chain homotopic to the identity — the hypothesis of the
small-simplices theorem (one uses a large enough iterate to force all chains into a given open
cover).

The affine-chain avatar of `sdChainMapIter X N` on the identity simplex of `Δⁿ` is
`Work.Cohomology.sdIterLC n N` (`Submission/Work/Cohomology/Mesh.lean`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The type of singular `n`-simplices of a topological space `X` (a shorthand avoiding the
simplex-category notation in downstream statements). -/
abbrev Simplex (X : TopCat) (n : ℕ) : Type := (TopCat.toSSet.obj X) _⦋n⦌

/-- The `N`-fold iterate of the subdivision chain map. -/
def sdChainMapIter (X : TopCat) (N : ℕ) : singularChains ℤ X ⟶ singularChains ℤ X :=
  match N with
  | 0 => CategoryTheory.CategoryStruct.id (singularChains ℤ X)
  | (N + 1) => CategoryTheory.CategoryStruct.comp (sdChainMapIter X N) (sdChainMap X)

theorem sdChainMapIter_zero (X : TopCat) :
    sdChainMapIter X 0 = CategoryTheory.CategoryStruct.id (singularChains ℤ X) := rfl

theorem sdChainMapIter_succ (X : TopCat) (N : ℕ) :
    sdChainMapIter X (N + 1)
      = CategoryTheory.CategoryStruct.comp (sdChainMapIter X N) (sdChainMap X) := rfl

/-- **Every iterate of the subdivision operator is chain homotopic to the identity.** -/
theorem sdChainMapIter_homotopic (X : TopCat) (N : ℕ) :
    Nonempty (Homotopy (sdChainMapIter X N)
      (CategoryTheory.CategoryStruct.id (singularChains ℤ X))) := by
  induction N with
  | zero => exact ⟨Homotopy.refl _⟩
  | succ N ih =>
    obtain ⟨h⟩ := ih
    obtain ⟨h3⟩ := sdHomotopy X
    exact ⟨(h.compRightId (sdChainMap X)).trans h3⟩

end

end Work.Cohomology
