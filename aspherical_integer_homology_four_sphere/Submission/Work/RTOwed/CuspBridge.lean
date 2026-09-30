/-
# The cusp block of the contract: the pending inputs of items 2, 3 and 4

Items 2, 3 and 4 of the contract are the parts of the atlas of `M̂` that belong to the area
`Submission/Work/Cusp/`: the filling charts (collar/cusp, polar and core charts on `M̂`), the
transitions between a transported fold chart and a collar chart, and the gluing homeomorphism
`τ_v : Tset ≃ₜ ∂(⊔_v [-1,1]² × T_v)`.

**State of the Cusp area** (checked by reading it): the coordinate maps themselves are delivered and
proved — `Work.Cusp.cuspCoordM`, `Work.Cusp.polarCoordM`, `Work.Cusp.coreCoordM` (definitions),
`Work.Cusp.cuspCoordM_continuous`, `Work.Cusp.cuspCoordM_injective` (for a box of side `≤ 1`),
`Work.Cusp.exists_cuspChart`, `Work.Cusp.exists_polarChartS`, `Work.Cusp.exists_coreChart`,
`Work.Cusp.cover_univ`, `Work.Cusp.strata_cover`, `Work.Cusp.isOpen_cuspBoxInterior`,
`Work.Cusp.isOpen_polarBox`, `Work.Cusp.isOpen_coreBox`, `Work.Cusp.exists_tauHomeo`,
`Work.Cusp.beta`, `Work.Cusp.polarToUHS_ThetaPolar`, and the assembly-level open embeddings
`Work.Cusp.isOpenEmbedding_cuspCoordM`, `Work.Cusp.exists_polarChartM`,
`Work.Cusp.exists_coreChartM`.  What is *not* delivered is the gluing datum itself: no inhabitant of
`Work.Cusp.CuspGlueData` for the concrete `M̄` (see §2.1 of the area notes), which is what every one
of those theorems about `M̂` is stated for; and the transition smoothness/isometry of the filling
charts has not been stated yet.

This file therefore *names* that pending input in one structure, `Work.RTOwed.CuspInputs`, in the
vocabulary of this area, and records exactly which delivered theorem of `Cusp` discharges each
field:

* `glue` — the `τ_v` homeomorphism; discharged by `Work.Cusp.CuspGlueData.glue_eq` together with
  the cover of `Tset` by the ceiling points (`Work.Cusp.CuspGlueData.mbarPt`,
  `Work.Cusp.exists_tauHomeo` for the torus side);
* `fill.fillChart` / `fill.fillLayer` / `fill.fill_anywhere` / `fill.fill_smooth` /
  `fill.fill_iso` / `fill.fill_ok` — the charts of `M̂` from `Work.Cusp.cuspCoordM`,
  `Work.Cusp.polarCoordM`, `Work.Cusp.coreCoordM` (through the pending open-embedding theorems
  `isOpenEmbedding_cuspCoordM`, `exists_polarChartM`, `exists_coreChartM`), with the layers
  `ChartLayer.uhs δ` (collar), `ChartLayer.warped P` (polar) and `ChartLayer.flat h₀` (core) and the
  region conditions from `Work.Cusp.cuspBox`, `Work.Cusp.polarBox`, `Work.Cusp.coreBox`;
* `fill.fill_cover` — discharged by `Work.Cusp.cover_univ`;
* `cross` — smoothness/isometry of the transitions between a transported fold chart and a collar
  chart; where `Work.HypModel.polarToUHS_isometry`, `Work.Cusp.beta` and the collar charts enter.

Everything that follows from a `CuspInputs` is proved here: the assembled `Owed` and the instance
`Work.Space.RTData`.  The *only* missing ingredient of the whole contract is the inhabitant of
`CuspInputs`.
-/
import Mathlib
import Submission.Work.RTOwed.FoldAnalytic
import Submission.Work.Cusp.All

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

open Work.FoldInst

/-- **The pending input of the areas `FoldInst`/`Cusp` for the atlas of `M̂`**: the gluing
homeomorphism `τ_v`, the filling charts with their metric layers and transitions, and the
cross transitions between a transported fold chart and a collar chart.

Each field names, in the docstring, the delivered theorem (or the still-pending theorem) of the
area `Cusp` that discharges it; see the module docstring for the full list. -/
structure CuspInputs where
  /-- **The gluing `τ_v`** (item 4): `Tset ≃ₜ ∂(⊔_v [-1,1]² × T_v)`; discharged by
  `Work.Cusp.CuspGlueData.glue_eq` / `Work.Cusp.exists_tauHomeo` (the ceiling
  `Work.Cusp.beta` presents the truncation torus as a graph over the cusp torus). -/
  glue : Work.RTInstance.GlueHomeo
  /-- **The filling charts of `M̂`** (item 2): the collar/cusp charts crossing the gluing
  (`Work.Cusp.cuspCoordM`, pending `Work.Cusp.isOpenEmbedding_cuspCoordM`), the polar charts
  (`Work.Cusp.polarCoordM`, pending `Work.Cusp.exists_polarChartM`) and the core charts
  (`Work.Cusp.coreCoordM`, pending `Work.Cusp.exists_coreChartM`), with their layers, their
  smoothness and isometry, the region conditions of `Work.Cusp.cuspBox`/`polarBox`/`coreBox` and
  the cover `Work.Cusp.cover_univ`. -/
  fill : Work.RTInstance.FillData (Work.RTInstance.assemblyOf glue)
  /-- **The cross transitions** (item 3): smoothness and isometry of the transitions between a
  transported fold chart and a collar chart, where `Work.HypModel.polarToUHS_isometry` and the
  ceiling `Work.Cusp.beta` enter. -/
  cross : Work.RTInstance.CrossData (Work.RTInstance.assemblyOf glue)
    (foldAnalytic.toFoldData glue) fill

namespace CuspInputs

variable (h : CuspInputs)

/-- **The `Owed` data of the assembled space `M̂`**, from the delivered fold charts and the pending
cusp block. -/
noncomputable def owed : Work.RTInstance.Owed (Work.RTInstance.assemblyOf h.glue) :=
  Work.RTInstance.owedOf h.glue foldAnalytic h.fill h.cross

/-- **The instance `Work.Space.RTData` of `M̂`**: the field `rt` of `Work.Final.FinalInputs`. -/
noncomputable def rtData : Work.Space.RTData := (owed h).toRTData

/-- **The curvature datum of `Work.Final.FinalInputs.curvLe_field`** (the `CurvModels` route). -/
noncomputable def modelCurvature :
    Work.CurvModels.ModelCurvature (rtData h).models := (owed h).modelCurvature

/-- The same datum through the curvature hypothesis of the atlas. -/
theorem toRTData_nonpos : Work.RTInstance.RTDataNonpos (rtData h) :=
  (owed h).toRTData_nonpos

end CuspInputs

end Work.RTOwed
