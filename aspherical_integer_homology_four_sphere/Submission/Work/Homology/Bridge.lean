import Submission.Work.Homology.Basic
import Submission.Work.Homology.Pairs
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Bridge to the ported `Work.Cohomology` subdivision/excision chapter

The fleet's `Submission/Work/Cohomology` chapter (imported here) develops barycentric subdivision,
the small-chains theorem, Mayer–Vietoris, excision and the homology of spheres and disc pairs, in
the *same* chain model as `Work.Homology`: its `singularChains ℤ X` is definitionally
`singChain ZMod X`, and its `subtypeIncl X A` is `incl A`.  The bridges below are therefore `rfl`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Homology

noncomputable section

/-- The singular chain complex of `Work.Cohomology` is the one of `Work.Homology`. -/
theorem singChain_eq (X : TopCat) : singChain ZMod X = Work.Cohomology.singularChains ℤ X := rfl

/-- The relative chain complex of `Work.Cohomology` is the one of `Work.Homology`. -/
theorem relChain_eq (X : TopCat) (A : Set X) :
    relChain ZMod X A = Work.Cohomology.relChains X A := rfl

/-- Relative homology in the two developments agree. -/
theorem relHomology_eq (k : ℕ) (X : TopCat) (A : Set X) :
    relHomology ZMod k X A = (Work.Cohomology.relChains X A).homology k := rfl

end

end Work.Homology
