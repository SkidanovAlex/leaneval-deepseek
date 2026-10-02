import Mathlib
import Submission.Work.LerayHirsch.Twist
import Submission.Work.LerayHirsch.TwistSumDefs
import Submission.Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_map
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The tensor product with a line bundle distributes over the direct sum

For a complex line bundle `L` and complex vector bundles `E`, `F` over a common base there is a
bundle isomorphism

`L ⊗ (E ⊕ F) ≅ (L ⊗ E) ⊕ (L ⊗ F)`.

In the gluing-data model of this workspace the two sides are the cores
`Work.LerayHirsch.twistCore L (Work.Whitney.whitneySum E F)` (cover `ιL × (ιE × ιF)`) and
`Work.Whitney.whitneySum (Work.LerayHirsch.twistCore L E) (Work.LerayHirsch.twistCore L F)`
(cover `(ιL × ιE) × (ιL × ιF)`); both have model fibre `ℂ^{n+p}` and the isomorphism is the
constant gauge `1` along the reindexing `Work.LerayHirsch.diagProdIndex`
(`Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_map`).  The substance is the identity
`Work.LerayHirsch.twistCore_whitneySum_coordChange`: on each chart the transition functions agree,
because the scalar `scl λ` multiplying a block-diagonal transition is not seen by the splitting
`Work.Whitney.sumFibreC`.
-/

namespace Work.LerayHirsch

theorem nonempty_bundleIso_twist_whitneySum {B : Type} [TopologicalSpace B]
    {ιL ιE ιF : Type} {n p : ℕ}
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin p)) ιF) :
    Nonempty (Work.Thom.BundleIso
      (Work.LerayHirsch.twistCore L (Work.Whitney.whitneySum E F))
      (Work.Whitney.whitneySum (Work.LerayHirsch.twistCore L E)
        (Work.LerayHirsch.twistCore L F))) := by
  refine nonempty_bundleIso_of_gauge_fibre_map
    (Work.LerayHirsch.twistCore L (Work.Whitney.whitneySum E F))
    (Work.Whitney.whitneySum (Work.LerayHirsch.twistCore L E)
      (Work.LerayHirsch.twistCore L F))
    (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin (n + p)))) diagProdIndex ?_ ?_ ?_
  · exact diagProdIndex_baseSet_twistSum L E F
  · exact diagProdIndex_indexAt_twistSum L E F
  · intro i b
    simpa using twistCore_whitneySum_coordChange L E F i b

end Work.LerayHirsch
