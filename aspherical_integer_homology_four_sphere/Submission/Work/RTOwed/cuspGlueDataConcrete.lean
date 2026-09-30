/-
# The gluing datum of each cusp of `M̂`, unconditionally

The missing inhabitant of `Work.Cusp.CuspGlueData`, for the concrete chart `Work.RTOwed.mbarLow`
and the concrete gluing `Work.RTOwed.glueData : Work.RTInstance.GlueHomeo` built in `instGlue.lean`.
All the chart fields are now **proved**, so this is the unconditional datum that every theorem of
the cusp chapter about `M̂` (the collar/polar/core charts, the cover `Work.Cusp.cover_univ`,
`Work.Cusp.exists_tauHomeo`, ...) is stated for.
-/
import Mathlib
import Submission.Work.RTOwed.cuspGlueData
import Submission.Work.RTOwed.mbarLow_isEmbedding
import Submission.Work.RTOwed.mbarLow_not_Tset

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

/-- **The gluing datum of the `v`-th cusp of `M̂`, unconditionally**: the concrete chart
`Work.RTOwed.mbarLow` at the concrete gluing `Work.RTOwed.glueData`, from the four proved fields of
the chart (`mbarLow_cont`, `mbarLow_inj`, `mbarLow_open`, `mbarLow_isEmbedding`, `mbarLow_not_Tset`)
and the coordinate formula of the gluing (`glueData_apply`). -/
noncomputable def cuspGlueData (v : Fin 5) :
    Work.Cusp.CuspGlueData (assemblyOf glueData) v :=
  cuspGlueDataOf v
    (fun c δ => mbarLow_cont v c δ)
    (fun c δ hδ => mbarLow_inj v c δ hδ)
    (fun c δ => mbarLow_open v c δ)
    (fun c δ hδ => mbarLow_isEmbedding v c δ hδ)
    (fun c δ => mbarLow_not_Tset v c δ)

end Work.RTOwed
