/-
# `Work.RTInstance`: the concrete instance `Work.Space.RTData` of `M̂`

`import Submission.Work.RTInstance.All` brings in the whole area.  The headline results are

* `Work.RTInstance.Owed` — the pending inputs of the areas `FoldInst` and `Cusp`, as explicit
  named hypotheses (`Work.RTInstance.FoldData`, `Work.RTInstance.FillData`,
  `Work.RTInstance.CrossData`), together with the gluing `Work.RTInstance.GlueHomeo`;
* `Work.RTInstance.assemblyOf` — the topological assembly `M̂ = M̄ ∪ ⊔_v [-1,1]² × T_v`;
* `Work.RTInstance.Owed.preAtlas` and `Work.RTInstance.Owed.toRTData` — the atlas of `M̂` with its
  models, isometry and smooth transitions, and the instance `Work.Space.RTData`;
* `Work.RTInstance.RTDataNonpos` and `Work.RTInstance.RTDataNonpos.hmodels` — the model curvature
  datum of `Work.Final.FinalInputs.curvLe_field`.

See `Submission/Work/RTInstance/NOTES.md` for the interface and what remains to be discharged.
-/
import Submission.Work.RTInstance.Basic
import Submission.Work.RTInstance.Models
import Submission.Work.RTInstance.posExt_pos
import Submission.Work.RTInstance.uhsModel_pos
import Submission.Work.RTInstance.warpedModelA_pos
import Submission.Work.RTInstance.flatModel_pos
import Submission.Work.RTInstance.ChartLayer_model_pos
import Submission.Work.RTInstance.LayerPos
import Submission.Work.RTInstance.CurvDatum
import Submission.Work.RTInstance.PreAtlas
import Submission.Work.RTInstance.exists_chartOfMbar
import Submission.Work.RTInstance.model_smooth
import Submission.Work.RTInstance.Instance
import Submission.Work.RTInstance.ModelCurv
import Submission.Work.RTInstance.FoldInstBridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

