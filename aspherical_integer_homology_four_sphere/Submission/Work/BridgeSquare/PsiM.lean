/-
# `BridgeSquare/PsiM.lean` — the explicit cellular -> singular comparison `Ψ_M`

`Work.BridgeSquare.PsiM` is the *choice-free* comparison chain map from the polytopal cell complex
`Gen.mbarCx` of the hyperbolic piece `M̄` to its singular chains, built from the **concrete** atlas
and realization (`Mbar.mbarAtlasOf`, `Mbar.mbarBoundaryCompat`, `Mbar.mbarRealData
Mbar.flagRel_face`) — never from the `Classical.choose`d `Mbar.mbarAtlas` / `Mbar.mbarReal`.

```
PsiM := (Mbar.mbarAtlasOf).zMap Mbar.mbarBoundaryCompat
          ≫ (Mbar.mbarRealData Mbar.flagRel_face).toDeltaSimplexMap.deltaChainMap
```

It is a quasi-isomorphism (`PsiM_quasiIso`), by `CellAtlas.zMap_quasiIso` (the cellular
comparison) and `DeltaHomology.deltaChainMap_quasiIso` (Hatcher 2.27).  This is the map through
which the truncation-supported cellular cycles of `WP-F` are transported to `H_*(M̄)`, and hence
the map that makes `(c)` of `Submission/Work/NOTES_LEAD_aspherical_bridge.md` provable.

We also record the truncation predicate `isTruncCell` of the plan: a cell of `Gen.mbarCx` is a
*truncation cell* when its root face of `Q̄` meets one of the five truncation facets (constraint
index `≥ 24`); these are exactly the cells whose `Ψ_M`-image lies in the truncation torus
`Tset = range cuspMap`.
-/
import Submission.Work.MbarHomology.Mbar.Assemble
import Submission.Work.MbarHomology.Mbar.AtlasCx
import Submission.Work.MbarHomology.Mbar.AtlasBoundary
import Submission.Work.MbarHomology.Mbar.mbarReal_exists
import Submission.Work.MbarHomology.CellAtlas.zMap_quasiIso
import Submission.Work.MbarHomology.Mbar.eA
import Submission.Work.MbarHomology.Qbar.QbarTightCheap
import Submission.Work.HomologyMV.Interface
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.chainD_comp
import Submission.Work.DeltaHomology.chainMapFun_comm
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.deltaChainMap_comm
import Submission.Work.DeltaHomology.deltaChainMapFun_natural
import Submission.Work.DeltaHomology.Realization
import Submission.Work.DeltaHomology.SkeletonDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.mem_skelSet_iff
import Submission.Work.DeltaHomology.isClosed_skelSet
import Submission.Work.DeltaHomology.barycenter_not_mem_skelSet_of_lt
import Submission.Work.DeltaHomology.SkelProps
import Submission.Work.DeltaHomology.SkelChain
import Submission.Work.DeltaHomology.GoodPairDefs
import Submission.Work.DeltaHomology.isIso_relHomologyMap_of_deformationRetract
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.SkeletonMap
import Submission.Work.DeltaHomology.chain_homology_isZero_of_dim_lt
import Submission.Work.DeltaHomology.isZero_chainX_of_dim_lt
import Submission.Work.DeltaHomology.Main
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.PunctSimplex
import Submission.Work.DeltaHomology.exists_deformationRetract_punctSkel
import Submission.Work.DeltaHomology.relHomology_iso_clopen_sum
import Submission.Work.DeltaHomology.skelQuotient_shortExact
import Submission.Work.DeltaHomology.skelQuotient_X_isZero
import Submission.Work.Homology.Basic
import Submission.Work.DeltaHomology.cell_relHomology_iso
import Submission.Work.DeltaHomology.relHomology_skel_succ_excision
import Submission.Work.DeltaHomology.relHomology_cell_splitting
import Submission.Work.DeltaHomology.CellClassMap
import Submission.Work.DeltaHomology.punctCell_eq_sdiff
import Submission.Work.DeltaHomology.simplexGenMap_isIso
import Submission.Work.DeltaHomology.cellClassMapCell_isIso
import Submission.Work.DeltaHomology.quasiOso_deltaChainMapSkel
import Submission.Work.DeltaHomology.quasiOso_deltaChainMap
import Submission.Work.DeltaHomology.eq_of_cls_eq_of_pos
import Submission.Work.DeltaHomology.exists_homeomorph_intCell
import Submission.Work.DeltaHomology.closure_skelSet_interior_punctSkel
import Submission.Work.DeltaHomology.relHomology_stdSimplexBoundary
import Submission.Work.DeltaHomology.isQuotientMap_punctToPiece
import Submission.Work.DeltaHomology.PunctSkelBasic
import Submission.Work.HomologyIso.Gen.Mbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.BridgeSquare

noncomputable section

/-- **The explicit cellular → singular comparison for `M̄`.** -/
def PsiM : Work.HomologyIso.Gen.mbarCx.toChainComplex ⟶
    Work.HomologyMV.singCx (TopCat.of Work.FoldInst.Mbar) :=
  (Work.MbarHomology.Mbar.mbarAtlasOf).zMap Work.MbarHomology.Mbar.mbarBoundaryCompat
    ≫ (Work.MbarHomology.Mbar.mbarRealData Work.MbarHomology.Mbar.flagRel_face).toDeltaSimplexMap.deltaChainMap

/-- `Ψ_M` is a quasi-isomorphism (cellular comparison + Hatcher 2.27). -/
theorem PsiM_quasiIso : QuasiIso PsiM := by
  have h1 : QuasiIso ((Work.MbarHomology.Mbar.mbarAtlasOf).zMap
      Work.MbarHomology.Mbar.mbarBoundaryCompat) :=
    Work.MbarHomology.CellAtlas.zMap_quasiIso _ Work.MbarHomology.Qbar.QbarCW_hasDdZero
      Work.MbarHomology.Qbar.QbarCW_hasAugZero Work.MbarHomology.QbarCW_locallySpherical
      Work.MbarHomology.Mbar.mbarBoundaryCompat
  have h2 : QuasiIso ((Work.MbarHomology.Mbar.mbarRealData
      Work.MbarHomology.Mbar.flagRel_face).toDeltaSimplexMap.deltaChainMap) :=
    Work.DeltaHomology.deltaChainMap_quasiIso _ _
  exact quasiIso_comp _ _ (hφ := h1) (hφ' := h2)

/-- **The truncation predicate**: the cell `e` of `Gen.mbarCx` in degree `n` is a truncation cell
when its root face of `Q̄` is tight on one of the five truncation facets (constraint index `≥ 24`).
These are the cells whose `Ψ_M`-image lies in the truncation torus `Tset = Set.range cuspMap`. -/
def isTruncCell (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) : Bool :=
  decide (∃ c : Fin 48, c ∈ Work.MbarHomology.qTightC (Work.MbarHomology.Mbar.rootCx n e).idx
    ∧ 24 ≤ c.val)

end

end Work.BridgeSquare
