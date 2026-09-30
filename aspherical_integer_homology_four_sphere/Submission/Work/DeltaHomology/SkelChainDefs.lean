import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.SkeletonDefs
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.Realization
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The comparison chain map on the skeleta

For a `Δ`-complex `K` with characteristic maps `χ` in a space `X`, the `k`-skeleton
`X^k = χ.skelSet k` is a subspace of `X`, and the comparison map restricts to a
chain map

`deltaChainMapSkelFun χ k : (K.skel k).chain ⟶ C_*(X^k; ℤ)`,

sending a simplex `σ` of the `k`-skeleton (i.e. of dimension `≤ k`) to the singular
simplex of the subspace `X^k` induced by `χ σ`.

This file contains the definitions; the two structural facts (that it is a chain
map, and that it is compatible with `deltaChainMap` through the inclusion
`X^k ⊆ X`) are `deltaChainMapSkelFun_comm` and `deltaChainMapSkelFun_compat`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Convexity
open Work.Homology

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

open scoped Simplicial

variable {K : DeltaCx} {X : TopCat}

/-- For a `j`-simplex of `K` with `j ≤ k`, the induced singular simplex of the
subspace `X^k = χ.skelSet k`. -/
def DeltaSimplexMap.chiInSkelSet (χ : DeltaSimplexMap K X) (k : ℕ) {j : ℕ} (h : j ≤ k)
    (σ : Fin (K.card j)) :
    (TopCat.toSSet.obj (TopCat.of (χ.skelSet k))).obj
      (Opposite.op (SimplexCategory.mk j)) :=
  (TopCat.toSSetObjEquiv (TopCat.of (χ.skelSet k)) (Opposite.op (SimplexCategory.mk j))).symm
    (χ.clsInSkelSet k h σ)

/-- The degreewise comparison map on the `k`-skeleton: the free module on the
simplices of `K.skel k` (dimension `≤ k`) maps to the singular chains of the
subspace `X^k` by `σ ↦ χ σ`. -/
def DeltaSimplexMap.deltaChainMapSkelFun (χ : DeltaSimplexMap K X) (k : ℕ) (j : ℕ) :
    (K.skel k).chainX j ⟶ (singChain ZMod (TopCat.of (χ.skelSet k))).X j :=
  if h : j ≤ k then
    Sigma.desc (fun σ : Fin ((K.skel k).card j) =>
      SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of (χ.skelSet k)))
        (χ.chiInSkelSet k h (skelMap K k σ)))
  else 0

/-- The degreewise comparison map on a basis simplex. -/
theorem DeltaSimplexMap.deltaChainMapSkelFun_chainι (χ : DeltaSimplexMap K X) {k j : ℕ}
    (h : j ≤ k) (σ : Fin ((K.skel k).card j)) :
    (K.skel k).chainι j σ ≫ χ.deltaChainMapSkelFun k j
      = SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of (χ.skelSet k)))
          (χ.chiInSkelSet k h (skelMap K k σ)) := by
  rw [DeltaSimplexMap.deltaChainMapSkelFun, dif_pos h]
  exact Limits.Sigma.ι_comp_desc _ σ

end

end Work.DeltaHomology
