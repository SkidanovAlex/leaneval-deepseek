import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.Realization
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.SkelChainDefs
import Submission.Work.DeltaHomology.deltaChainMapSkelFun_comm
import Submission.Work.DeltaHomology.deltaChainMapSkelFun_compat
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The comparison chain map on the skeleta

Assembles, from the degreewise data of
`Submission/Work/DeltaHomology/SkelChainDefs.lean`, the comparison chain map

`deltaChainMapSkel χ k : (K.skel k).chain ⟶ C_*(X^k; ℤ)`

of the `k`-skeleton, together with its compatibility with the comparison map of `K`
through the inclusions `K.skel k ⟶ K` and `X^k ⟶ X`:

`deltaChainMapSkel_compat :
  χ.deltaChainMapSkel k ≫ inclChain ℤ X (χ.skelSet k)
    = chainMap (K.skelHom k) ≫ χ.deltaChainMap`.

This is the chain-level input for the skeleta induction of Hatcher's theorem.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Convexity
open Work.Homology

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

open scoped Simplicial

variable {K : DeltaCx} {X : TopCat}

/-- The comparison chain map on the `k`-skeleton. -/
def DeltaSimplexMap.deltaChainMapSkel (χ : DeltaSimplexMap K X) (k : ℕ) :
    (K.skel k).chain ⟶ singChain ZMod (TopCat.of (χ.skelSet k)) :=
  ChainComplex.ofHom (χ.deltaChainMapSkelFun k) fun j => by
    rw [DeltaCx.chain_d]
    exact deltaChainMapSkelFun_comm χ k j

@[simp]
theorem DeltaSimplexMap.deltaChainMapSkel_f (χ : DeltaSimplexMap K X) (k j : ℕ) :
    (χ.deltaChainMapSkel k).f j = χ.deltaChainMapSkelFun k j := rfl

/-- The comparison chain map on the `k`-skeleton is compatible with the
comparison map of `K` through the inclusions of the skeleton into `K` and of the
skeleton space into `X`. -/
theorem DeltaSimplexMap.deltaChainMapSkel_compat (χ : DeltaSimplexMap K X) (k : ℕ) :
    χ.deltaChainMapSkel k ≫ inclChain ZMod X (χ.skelSet k)
      = DeltaCx.Hom.chainMap (K.skelHom k) ≫ χ.deltaChainMap := by
  apply HomologicalComplex.Hom.ext
  funext j
  simpa only [HomologicalComplex.comp_f, DeltaSimplexMap.deltaChainMapSkel_f,
    DeltaCx.Hom.chainMap_f, DeltaSimplexMap.deltaChainMap_f, DeltaCx.chain_X] using
    deltaChainMapSkelFun_compat χ k j

end

end Work.DeltaHomology
