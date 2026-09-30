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
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.exists_coreChartM
import Submission.Work.Cusp.MChartAux
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner
import Submission.Work.Cusp.exists_polarChartS
import Submission.Work.Cusp.isOpen_polarBox
import Submission.Work.Cusp.isOpenEmbedding_incW_interior
import Submission.Work.Cusp.isOpenMap_fillProj
import Submission.Work.Cusp.isOpen_polarTargetS
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.isOpen_cuspChartBox
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.cuspCoordM_continuous
import Submission.Work.Cusp.cuspCoordM_injective
import Submission.Work.Cusp.isOpenEmbedding_layerPtSq
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.continuous_cuspCollarInv
import Submission.Work.Cusp.collarHeight_half
import Submission.Work.Space.Assembly
import Submission.Work.Cusp.ChartTop
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.Data
import Submission.Work.Cusp.ThetaCore_add_int
import Submission.Work.Cusp.ThetaCore_continuous
import Submission.Work.Cusp.ThetaCore_cuspInvCore
import Submission.Work.Cusp.invY_wOf
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.nrm_nonneg
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.uPerim_mem
import Submission.Work.Cusp.nrm_u_injOn
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.radial_eq_inner
import Submission.Work.Cusp.radial_collar
import Submission.Work.Cusp.collarHeight_pos
import Submission.Work.Cusp.ThetaOuter_add_int
import Submission.Work.Cusp.collarHeight_one
import Submission.Work.Cusp.bndOfU_uPerim
import Submission.Work.Cusp.nrm_continuous
import Submission.Work.Cusp.ThetaPolarS_continuousOn
import Submission.Work.Cusp.beta_continuous
import Submission.Work.Cusp.ThetaOuter_cuspInvOuter
import Submission.Work.Cusp.ThetaOuter_injOn
import Submission.Work.Cusp.ThetaPolarS_uScont
import Submission.Work.Cusp.wOf_add
import Submission.Work.Cusp.ThetaPolar_cuspInvInner
import Submission.Work.Cusp.collarHeight_strictAntiOn
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.TopWindow
import Submission.Work.Cusp.WedgeSCone
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.Cusp.beta_add_int
import Submission.Work.Cusp.beta_add_smul_slope
import Submission.Work.Cusp.beta_cuspX_fract
import Submission.Work.Cusp.beta_lattice_periodic
import Submission.Work.Cusp.beta_min_le
import Submission.Work.Cusp.bndOfU_add_int
import Submission.Work.Cusp.bndOfU_add_quarter
import Submission.Work.Cusp.bndOfU_mem
import Submission.Work.Cusp.bndOfU_u
import Submission.Work.Cusp.bnd_eq_self
import Submission.Work.Cusp.collarHeight_inv
import Submission.Work.Cusp.collarHeight_mem
import Submission.Work.Cusp.cuspInvOuter_ThetaOuter_half
import Submission.Work.Cusp.continuous_cuspTopF
import Submission.Work.Cusp.continuous_cuspTopInv
import Submission.Work.Cusp.exists_section_box
import Submission.Work.Cusp.cuspInvCore_ThetaCore
import Submission.Work.Cusp.cuspInvCore_mem_coreStratum
import Submission.Work.Cusp.cover_univ
import Submission.Work.Cusp.cover_univ_charts
import Submission.Work.Cusp.cuspCoordMTop_continuous
import Submission.Work.Cusp.cuspCoordMTop_injective
import Submission.Work.Cusp.cuspInvCore_continuousOn
import Submission.Work.Cusp.cuspInvInner_ThetaPolar
import Submission.Work.Cusp.cuspInvInner_ThetaPolarS
import Submission.Work.Cusp.cuspInvInner_add_int_mul_two_pi
import Submission.Work.Cusp.cuspInvInner_continuousOn
import Submission.Work.Cusp.cuspInvInner_mem_polarStratum
import Submission.Work.Cusp.cuspInvInner_nrm
import Submission.Work.Cusp.cuspInvInner_nrm_gt
import Submission.Work.Cusp.cuspInvInner_uqOf
import Submission.Work.Cusp.outerU_cuspX
import Submission.Work.Cusp.outerY_cuspX
import Submission.Work.Cusp.cuspInvOuter_continuousOn
import Submission.Work.Cusp.cuspInvOuter_height
import Submission.Work.Cusp.cuspInvOuter_heightTop
import Submission.Work.Cusp.cuspInvOuter_mem_Sq
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop
import Submission.Work.Cusp.cuspInvOuter_mem_cuspStratum
import Submission.Work.Cusp.cuspInvOuter_nrm_eq_one_ceilingTop
import Submission.Work.Cusp.cuspTopF_apply_cuspTopInv
import Submission.Work.Cusp.cuspTopInv_apply_cuspTopF
import Submission.Work.Cusp.cuspTopUp_eq
import Submission.Work.Cusp.cuspX_injOn
import Submission.Work.Cusp.cuspX_outerU_outerY
import Submission.Work.Cusp.isOpen_coreBox
import Submission.Work.Cusp.isOpen_cuspBoxInterior
import Submission.Work.Cusp.uS_continuousOn_wedgeS
import Submission.Work.Cusp.isOpen_wedgeS
import Submission.Work.Cusp.slope_lattice
import Submission.Work.Cusp.mbarPt_periodic
import Submission.Work.Cusp.s1_lt_betaMin
import Submission.Work.Cusp.mbarPt_eq_iff
import Submission.Work.Cusp.exp_radial_collar
import Submission.Work.Cusp.frame_orthonormal
import Submission.Work.Cusp.geo_quarter
import Submission.Work.Cusp.isOpenEmbedding_cuspCoordMTop
import Submission.Work.Cusp.isOpenEmbedding_cuspTopF
import Submission.Work.Cusp.isOpenEmbedding_layerPtI
import Submission.Work.Cusp.isOpenMap_cuspTopUp
import Submission.Work.Cusp.isOpen_cuspBoxTop
import Submission.Work.Cusp.isOpen_polarSourceS
import Submission.Work.Cusp.kv_ne_zero
import Submission.Work.Cusp.mem_range_cuspTopF
import Submission.Work.Cusp.nrm_le_one
import Submission.Work.Cusp.outerU_axis
import Submission.Work.Cusp.outerU_continuous
import Submission.Work.Cusp.uqOf_ThetaPolarS
import Submission.Work.Cusp.polarToUHS_ThetaPolar
import Submission.Work.Cusp.radial_bounds
import Submission.Work.Cusp.wedge_cover
import Submission.Work.Cusp.radial_half
import Submission.Work.Cusp.slope_ne_zero
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.uPerim_corner_approx
import Submission.Work.Cusp.uS_lift
import Submission.Work.Cusp.u_continuousAt_off_corner
import Submission.Work.Cusp.u_mem
import Submission.Work.Cusp.u_mem_univ
import Submission.Work.Cusp.u_smul
import Submission.Work.Cusp.wOf_invY

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
