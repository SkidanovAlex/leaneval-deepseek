/-
# The completed instance code of `Submission/Work/RTInstance/NOTES.md` §2

NOTES.md §2 of the area `RTInstance` writes the completion of the instance as

```lean
-- g : Work.RTInstance.GlueHomeo                            (the CUSP gluing τ_v)
-- A : Work.RTInstance.FoldAnalytic                         (§4.1)
-- G : Work.RTInstance.FillData (assemblyOf g)              (§4.2)
-- C : Work.RTInstance.CrossData (assemblyOf g) (A.toFoldData g) G   (§4.3)
noncomputable def h : Work.RTInstance.Owed (assemblyOf g) := owedOf g A G C

instance : Work.Space.RTData := h.toRTData
instance : Work.CurvModels.ModelCurvature h.toRTData.models := h.modelCurvature
```

In this file the fold block `A` is *discharged*: `Work.RTOwed.foldAnalytic` is an actual element of
`Work.RTInstance.FoldAnalytic` (`Work.RTOwed.FoldAnalytic.lean`).  The remaining inputs are the
`GlueHomeo`, `FillData` and `CrossData` of the area `Cusp`, which are bundled in
`Work.RTOwed.CuspInputs` (see `Work.RTOwed.CuspBridge`); the two `instance` lines above are
therefore written below as the definitions `Work.RTOwed.owedsOf`, `Work.RTOwed.rtDataOf` and
`Work.RTOwed.modelCurvatureOf`, and become literal `instance` declarations as soon as
`CuspInputs` is inhabited.

The fold data of the concrete assembly, with the fold block already filled in, is
`Work.RTOwed.foldDataOf`: it is the `F` field of `Owed (assemblyOf g)`.
-/
import Mathlib
import Submission.Work.RTOwed.CuspBridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter Matrix
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace Matrix
open Bundle

namespace Work.RTOwed

open Work.RTInstance

/-- **The fold block of the atlas of `M̂`**: `Work.FoldInst.foldChart` with the three analytic facts
of item 1 (`Work.RTOwed.foldAnalyticOf`), as the `FoldData` of the concrete assembly. -/
noncomputable def foldDataOf (g : GlueHomeo) : FoldData (assemblyOf g) :=
  foldAnalytic.toFoldData g

/-- **The `Owed` data of `M̂` from the two remaining inputs** (the glue homeomorphism and the cusp
charts, bundled in `CuspInputs`). -/
noncomputable def owedOf (h : CuspInputs) : Owed (assemblyOf h.glue) :=
  Work.RTInstance.owedOf h.glue foldAnalytic h.fill h.cross

/-- The fold block of that `Owed` data is `foldDataOf`. -/
theorem owedOf_F (h : CuspInputs) : (owedOf h).F = foldDataOf h.glue := rfl

/-- **The instance `Work.Space.RTData` of `M̂`** — the field `rt` of `Work.Final.FinalInputs`. -/
noncomputable def rtDataOf (h : CuspInputs) : Work.Space.RTData := (owedOf h).toRTData

/-- **The curvature datum of `Work.Final.FinalInputs.curvLe_field`** (the `CurvModels` route). -/
noncomputable def modelCurvatureOf (h : CuspInputs) :
    Work.CurvModels.ModelCurvature (rtDataOf h).models := (owedOf h).modelCurvature

/-- The same datum through the area's own non-positivity hypothesis. -/
theorem rtDataOf_nonpos (h : CuspInputs) : RTDataNonpos (rtDataOf h) :=
  (owedOf h).toRTData_nonpos

/-- **The abstract statement that remains**: if the pending cusp block `CuspInputs` is inhabited,
then the instance of `Work.Space.RTData` exists (and hence `Work.Final.FinalInputs` owes only its
homological and smoothness fields; its `rt` and `curvLe` fields are produced here). -/
theorem rtData_exists : Nonempty CuspInputs → Nonempty Work.Space.RTData :=
  fun ⟨h⟩ => ⟨rtDataOf h⟩

end Work.RTOwed
