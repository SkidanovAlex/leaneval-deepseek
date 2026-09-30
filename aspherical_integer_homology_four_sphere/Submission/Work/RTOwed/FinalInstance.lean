/-
# The unconditional instance `Work.Space.RTData` of `M̂`

This is the completion of `Submission/Work/RTInstance/NOTES.md` §2: with

* the gluing `Work.RTOwed.glueData : Work.RTInstance.GlueHomeo` (item 4, `instGlue`),
* the gluing datum `Work.RTOwed.cuspGlueData v : Work.Cusp.CuspGlueData (assemblyOf glueData) v`
  (the missing inhabitant of the cusp chapter, `cuspGlueDataConcrete`),
* the rigidity `Work.RTOwed.cuspRigid_glueData` (F1/F2/F3 of `Work.RTOwed.CuspRigid`), and
* `Work.RTOwed.fillCross_of_rigid` — the filling charts of `M̂` with their layer covers (item 2)
  together with the cross transitions to the fold charts (item 3),

the cusp block `Work.RTOwed.CuspInputs` is inhabited, hence so is `Work.RTInstance.Owed`, and the
two instances of the contract hold **unconditionally**.

## What to import

`import Submission.Work.RTOwed.FinalInstance` (or `Submission.Work.RTOwed.All`), then use

* `Work.RTOwed.cuspInputs : Work.RTOwed.CuspInputs`,
* `Work.RTOwed.rtData : Work.Space.RTData` (the field `rt` of `Work.Final.FinalInputs`),
* `Work.RTOwed.modelCurvature : Work.CurvModels.ModelCurvature rtData.models`
  (whence `Work.Final.FinalInputs.curvLe_field` via `Work.CurvModels.hmodels`,
  or `Work.RTOwed.rtData_nonpos` via `Work.RTInstance.RTDataNonpos`),
* the global instances `instance : Work.Space.RTData` and
  `instance : Work.CurvModels.ModelCurvature Work.RTOwed.rtData.models`.
-/
import Mathlib
import Submission.Work.RTOwed.fillCross_of_rigid
import Submission.Work.RTOwed.cuspRigidGlueData
import Submission.Work.RTOwed.Instance

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTOwed

open Work.RTInstance

/-- **The filling charts of `M̂` and their cross transitions, unconditionally** (items 2 and 3 of
the contract). -/
noncomputable def fillCross : Work.RTOwed.FillCross Work.RTOwed.glueData :=
  (fillCross_of_rigid Work.RTOwed.glueData Work.RTOwed.cuspGlueData
    Work.RTOwed.cuspRigid_glueData).some

/-- **The cusp block of the contract, unconditionally.** -/
noncomputable def cuspInputs : Work.RTOwed.CuspInputs where
  glue := Work.RTOwed.glueData
  fill := (fillCross).charts.toFillData (Work.RTOwed.foldDataOf Work.RTOwed.glueData)
  cross := (fillCross).cross

/-- **The instance `Work.Space.RTData` of `M̂`** — the field `rt` of `Work.Final.FinalInputs`. -/
noncomputable def rtData : Work.Space.RTData := Work.RTOwed.rtDataOf cuspInputs

/-- **The curvature datum of `Work.Final.FinalInputs.curvLe_field`** (the `CurvModels` route). -/
noncomputable def modelCurvature : Work.CurvModels.ModelCurvature rtData.models :=
  Work.RTOwed.modelCurvatureOf cuspInputs

/-- The same datum through the curvature hypothesis of the atlas. -/
theorem rtData_nonpos : Work.RTInstance.RTDataNonpos rtData :=
  Work.RTOwed.rtDataOf_nonpos cuspInputs

instance : Work.Space.RTData := rtData

instance : Work.CurvModels.ModelCurvature rtData.models := modelCurvature

end Work.RTOwed
