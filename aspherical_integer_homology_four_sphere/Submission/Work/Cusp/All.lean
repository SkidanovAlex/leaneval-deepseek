/-
# The cusp chapter: everything at once

`import Submission.Work.Cusp.All` brings in the definitions (`Work.Cusp.Basic`, `Work.Cusp.Charts`,
`Work.Cusp.Data`, `Work.Cusp.TopBox`, `Work.Cusp.TopLayer`, `Work.Cusp.Assembly`,
`Work.Cusp.MChartAux`, `Work.Cusp.CuspChartAux`, `Work.Cusp.CuspCollarAux`) and every lemma of the
chapter, including the charts of `M̂` (`Work.Cusp.ChartTop`, `Work.Cusp.ChartMhat`).  See the module
docstrings of `Basic`, `Charts`, `TopBox` and `Assembly` for the conventions, and the report of the
area for the interface.

## The charts of `M̂` and the cover theorem

* `cuspChart a v D c δ hδ` (`ChartTop`) — the **collar chart**, on the *unslabbed* box
  `cuspBoxTop v c δ = {side 2δ around c in x, heights in (s₁, sTop)}`; the family which covers the
  whole collar layer `‖p‖∞ ≥ 1/2` of every cusp, including the four corner directions of the filling
  square (`u(p) ∈ ℤ`) and the junction `‖p‖∞ = 1/2`.  API: `cuspChart_source` (the source is
  `Set.range (cuspCoordMTop a v D c δ)`), `cuspChart_target`, `cuspChart_apply`, `cuspChart_symm`.
* `cuspChartSlab a v D c δ hδ` (`ChartMhat`) — the *slabbed* collar chart on the box
  `cuspChartBox v c δ` (meridian slab `0 < outerU v x < 1`, window `(s₁, s_J)`); it does **not**
  cover the collar (this is why the unslabbed family above exists) and is kept for reference.
* `polarChart a v tor c k W hW hsec` and `coreChart a v tor W hW hsec` (`ChartMhat`) — the polar
  charts of the (inner) annulus and the core charts of the filling piece, over a `w`-box `W` which
  is a local section of `ℝ² → (ℝ/ℤ)²` (`hsec`, produced by `Work.Cusp.exists_section_box`); their
  sources are `Set.range (polarCoordM …)`, resp. `Set.range (coreCoordM …)`.
* `cover_univ_charts` / `fill_cover_of_layer_cover` (`cover_univ_charts`) — **the cover theorem**:
  the union of the sources of the fold, collar, polar and core charts is `univ`, given that the fold
  charts cover `M̄ ∖ Tset`, that the collar charts cover `{‖p‖∞ ≥ 1/2}`, that the polar charts cover
  `{1/24 < ‖p‖∞ < 1/2}` and that the core charts cover `{‖p‖∞ < 1/12}`.  The layer-level statement
  (independent of charts) is `cover_univ`; the three layer hypotheses are *discharged pointwise* for
  the concrete families by `collarLayer_subset_range_cuspCoordMTop`,
  `polarLayer_subset_range_polarCoordM` and `coreLayer_subset_range_coreCoordM`.

## The main results (all in namespace `Work.Cusp`)

* the ceiling `beta`: `beta_pos`, `beta_min_le`, `beta_le_max`, `beta_continuous`,
  `beta_add_int`, `beta_lattice_periodic`, `beta_add_smul_slope`, `s1_lt_betaMin`,
  `betaMax_lt_sJ`, and the collar window `sTop = 33/20` with `sJ_lt_sTop`, `betaMax_lt_sTop`,
  `betaMax_mul_sTop_lt_sJ_sq`, `betaMax_mul_sTop_sq_lt_sJ_cu` (`TopWindow`);
* the perimeter parameter `u`: `u_mem`, `bndOfU_uPerim`, `uPerim_bndOfU`, `bndOfU_u`, `u_smul`,
  `nrm_u_injOn`, `u_continuousOn_wedge`, `isOpen_wedge`, `wedge_cover`, and the shifted lift
  `uS_zero`, `uS_lift`, `uS_mem`, `uS_continuousOn_wedgeS`, `isOpen_wedgeS`;
* the cusp coordinates and the frame: `kappa_orthogonal`, `frame_orthonormal`, `outerU_cuspX`,
  `outerY_cuspX`, `cuspX_outerU_outerY`, `outerU_zero`…`outerU_four`, `abs_outerU_sub_lt_of`,
  `wDet_ne_zero`, `wOf_invY`, `invY_wOf`;
* the chart maps `ThetaOuter`, `ThetaPolar` (`ThetaPolarS`), `ThetaCore`: `*_continuousOn`,
  `*_injOn`, `ThetaOuter_apply_one`, `polarToUHS_ThetaPolar` (the junction),
  `ThetaOuter_add_int`, `collarHeight_mem`;
* the explicit inverses `cuspInvOuter`, `cuspInvInner`, `cuspInvCore` with the round trips
  `ThetaOuter_cuspInvOuter`, `cuspInvOuter_ThetaOuter` (and `_half`, for the junction),
  `ThetaPolar_cuspInvInner`, `ThetaPolarS_cuspInvInner`, `cuspInvInner_ThetaPolar`,
  `cuspInvInner_ThetaPolarS`, `ThetaCore_cuspInvCore`, `cuspInvCore_ThetaCore`, and the lattice
  equivariances `ThetaPolar_add_int`, `ThetaCore_add_int`, `cuspInvInner_add_int_mul_two_pi`;
* **the truncation torus `τ_v`**: `exists_tauHomeo` (the cusp torus as the graph of the ceiling
  over `ℝ³/Λ_v`), `isClosed_range_tauCoord`, `tauCoord_injective`, `lattice_eq_closure_slope`
  (`Λ_v = ℤσ_v ⊕ ℤλ₂ ⊕ ℤλ₃`, the `(σ_v,λ₂,λ₃)`-coordinates), and — for the ceiling map `mbarPt` of
  the gluing datum — `mbarPt_periodic`, `mbarPt_continuous`, `mbarPt_eq_iff`
  (`mbarPt x = mbarPt x' ↔ x − x' ∈ Λ_v`) and `exists_tauHomeoMbar`:
  `∃ Φ : ℝ³/Λ_v ≃ₜ Set.range D.mbarPt` with `Φ (mk x) = mbarPt x`, the coordinate form of
  `τ_v : ℝ³/Λ_v ≃ₜ T_v ⊆ M̄`;
* the W-level charts: `exists_cuspChart`, `exists_polarChart(S)`, `exists_coreChart`
  (`OpenPartialHomeomorph` of the `(p,y)`-cover of a filling piece, with explicit inverses);
* the sources of the stratum cover: `strata_cover`, `W_cover`, `wedge_cover`;
* the **unslabbed collar family** (`TopBox`, `TopLayer`, `cuspInvOuter_mem_SqTop`,
  `cuspInvOuter_heightTop`, `beta_cuspX_fract`, `isOpenEmbedding_layerPtI`): the box `cuspBoxTop`,
  the collar source `cuspSourceTop`, the meridian anchor `cuspAnchor v c = outerU v c − 1/2`, the
  layer window `layerLo = 1/4`, the layer chart `layerPtI a` on `(a,a+1) × (1/4,1]`, the collar
  coordinates `cuspTopF` and their continuous inverse `cuspTopInv`, the recovered layer parameter
  `cuspInvOuter_nrm_Top : 1/4 < ‖(cuspInvOuter v q).1‖∞ ≤ 1`, the ceiling characterisation
  `cuspInvOuter_nrm_eq_one_ceilingTop`, and the coordinate inclusion `cuspCoordMTop` of `M̂` with
  `isOpenEmbedding_cuspCoordMTop`.
-/
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.ChartMhat
import Submission.Work.Cusp.ChartTop
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.Data
import Submission.Work.Cusp.MChartAux
import Submission.Work.Cusp.ThetaCore_add_int
import Submission.Work.Cusp.ThetaCore_continuous
import Submission.Work.Cusp.ThetaCore_cuspInvCore
import Submission.Work.Cusp.ThetaCore_eq_polar
import Submission.Work.Cusp.ThetaCore_injOn
import Submission.Work.Cusp.ThetaOuter_add_int
import Submission.Work.Cusp.ThetaOuter_apply_one
import Submission.Work.Cusp.ThetaOuter_continuousOn
import Submission.Work.Cusp.ThetaOuter_cuspInvOuter
import Submission.Work.Cusp.ThetaOuter_injOn
import Submission.Work.Cusp.ThetaPolarS_continuousOn
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner
import Submission.Work.Cusp.ThetaPolarS_uScont
import Submission.Work.Cusp.ThetaPolarS_zero
import Submission.Work.Cusp.ThetaPolar_add_int
import Submission.Work.Cusp.ThetaPolar_continuousOn_wedge
import Submission.Work.Cusp.ThetaPolar_cuspInvInner
import Submission.Work.Cusp.ThetaPolar_injOn
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.TopWindow
import Submission.Work.Cusp.W_cover
import Submission.Work.Cusp.WedgeSCone
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.beta_add_int
import Submission.Work.Cusp.beta_add_smul_slope
import Submission.Work.Cusp.beta_continuous
import Submission.Work.Cusp.beta_cuspX_fract
import Submission.Work.Cusp.beta_lattice_mem_slope
import Submission.Work.Cusp.beta_lattice_periodic
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.beta_min_le
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.bndOfU_add_int
import Submission.Work.Cusp.bndOfU_add_quarter
import Submission.Work.Cusp.bndOfU_mem
import Submission.Work.Cusp.bndOfU_u
import Submission.Work.Cusp.bndOfU_uPerim
import Submission.Work.Cusp.bnd_eq_self
import Submission.Work.Cusp.bnd_mem
import Submission.Work.Cusp.collarHeight_half
import Submission.Work.Cusp.collarHeight_inv
import Submission.Work.Cusp.collarHeight_mem
import Submission.Work.Cusp.collarHeight_one
import Submission.Work.Cusp.collarHeight_pos
import Submission.Work.Cusp.collarHeight_strictAntiOn
import Submission.Work.Cusp.collarLayer_subset_range_cuspCoordMTop
import Submission.Work.Cusp.continuous_cuspCollarF
import Submission.Work.Cusp.continuous_cuspCollarInv
import Submission.Work.Cusp.continuous_cuspTopF
import Submission.Work.Cusp.continuous_cuspTopInv
import Submission.Work.Cusp.coreLayer_subset_range_coreCoordM
import Submission.Work.Cusp.cover_univ
import Submission.Work.Cusp.cover_univ_charts
import Submission.Work.Cusp.cuspCollarInv_apply_cuspCollarF
import Submission.Work.Cusp.cuspCoordMTop_continuous
import Submission.Work.Cusp.cuspCoordMTop_injective
import Submission.Work.Cusp.cuspCoordM_continuous
import Submission.Work.Cusp.cuspCoordM_injective
import Submission.Work.Cusp.cuspInvCore_ThetaCore
import Submission.Work.Cusp.cuspInvCore_continuousOn
import Submission.Work.Cusp.cuspInvCore_mem_coreStratum
import Submission.Work.Cusp.cuspInvInner_ThetaPolar
import Submission.Work.Cusp.cuspInvInner_ThetaPolarS
import Submission.Work.Cusp.cuspInvInner_add_int_mul_two_pi
import Submission.Work.Cusp.cuspInvInner_continuousOn
import Submission.Work.Cusp.cuspInvInner_mem_polarStratum
import Submission.Work.Cusp.cuspInvInner_nrm
import Submission.Work.Cusp.cuspInvInner_nrm_gt
import Submission.Work.Cusp.cuspInvInner_uqOf
import Submission.Work.Cusp.cuspInvOuter_ThetaOuter
import Submission.Work.Cusp.cuspInvOuter_ThetaOuter_half
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
import Submission.Work.Cusp.exists_coreChart
import Submission.Work.Cusp.exists_coreChartM
import Submission.Work.Cusp.exists_cuspChart
import Submission.Work.Cusp.exists_polarChart
import Submission.Work.Cusp.exists_polarChartM
import Submission.Work.Cusp.exists_polarChartS
import Submission.Work.Cusp.exists_section_box
import Submission.Work.Cusp.exists_tauHomeo
import Submission.Work.Cusp.exists_tauHomeoMbar
import Submission.Work.Cusp.exp_radial_collar
import Submission.Work.Cusp.fract_uS
import Submission.Work.Cusp.frame1_smul
import Submission.Work.Cusp.frame_orthonormal
import Submission.Work.Cusp.geo_quarter
import Submission.Work.Cusp.invY_wOf
import Submission.Work.Cusp.isClosed_range_tauCoord
import Submission.Work.Cusp.isOpenEmbedding_cuspCollarF
import Submission.Work.Cusp.isOpenEmbedding_cuspCoordM
import Submission.Work.Cusp.isOpenEmbedding_cuspCoordMTop
import Submission.Work.Cusp.isOpenEmbedding_cuspInvInner_polarBoxSect
import Submission.Work.Cusp.isOpenEmbedding_cuspTopF
import Submission.Work.Cusp.isOpenEmbedding_incW_interior
import Submission.Work.Cusp.isOpenEmbedding_layerPtI
import Submission.Work.Cusp.isOpenEmbedding_layerPtSq
import Submission.Work.Cusp.isOpenEmbedding_polarCoordM
import Submission.Work.Cusp.isOpenMap_cuspTopUp
import Submission.Work.Cusp.isOpenMap_fillProj
import Submission.Work.Cusp.isOpen_coreBox
import Submission.Work.Cusp.isOpen_cuspBoxInterior
import Submission.Work.Cusp.isOpen_cuspBoxTop
import Submission.Work.Cusp.isOpen_cuspChartBox
import Submission.Work.Cusp.isOpen_nrm_gt
import Submission.Work.Cusp.isOpen_nrm_lt
import Submission.Work.Cusp.isOpen_polarBox
import Submission.Work.Cusp.isOpen_polarSourceS
import Submission.Work.Cusp.isOpen_polarTargetS
import Submission.Work.Cusp.isOpen_wedge
import Submission.Work.Cusp.isOpen_wedgeS
import Submission.Work.Cusp.kappa_orthogonal
import Submission.Work.Cusp.kv_ne_zero
import Submission.Work.Cusp.mbarPt_continuous
import Submission.Work.Cusp.mbarPt_eq_iff
import Submission.Work.Cusp.mbarPt_periodic
import Submission.Work.Cusp.mem_range_cuspCollarF
import Submission.Work.Cusp.mem_range_cuspTopF
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.nrm_continuous
import Submission.Work.Cusp.nrm_le_one
import Submission.Work.Cusp.nrm_nonneg
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_u_injOn
import Submission.Work.Cusp.nrm_u_injOn_univ
import Submission.Work.Cusp.off_continuous
import Submission.Work.Cusp.off_eq_infDist
import Submission.Work.Cusp.outerU_axis
import Submission.Work.Cusp.outerU_continuous
import Submission.Work.Cusp.outerU_cuspX
import Submission.Work.Cusp.outerY_cuspX
import Submission.Work.Cusp.polarBoxSect_aux
import Submission.Work.Cusp.polarLayer_subset_range_polarCoordM
import Submission.Work.Cusp.polarToUHS_ThetaPolar
import Submission.Work.Cusp.radial_bounds
import Submission.Work.Cusp.radial_collar
import Submission.Work.Cusp.radial_continuousOn
import Submission.Work.Cusp.radial_eq_inner
import Submission.Work.Cusp.radial_half
import Submission.Work.Cusp.radial_le_four
import Submission.Work.Cusp.s1_lt_betaMin
import Submission.Work.Cusp.slope_dot_cuspY
import Submission.Work.Cusp.slope_lattice
import Submission.Work.Cusp.slope_ne_zero
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.strata_cover
import Submission.Work.Cusp.tauCoord_injective
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.uPerim_corner_approx
import Submission.Work.Cusp.uPerim_mem
import Submission.Work.Cusp.uS_continuousOn_wedgeS
import Submission.Work.Cusp.uS_lift
import Submission.Work.Cusp.uS_mem
import Submission.Work.Cusp.uS_zero
import Submission.Work.Cusp.u_continuousAt_off_corner
import Submission.Work.Cusp.u_continuousOn_wedge
import Submission.Work.Cusp.u_eq_of_cos_sin_eq
import Submission.Work.Cusp.u_mem
import Submission.Work.Cusp.u_mem_univ
import Submission.Work.Cusp.u_smul
import Submission.Work.Cusp.uqOf_ThetaPolarS
import Submission.Work.Cusp.wDet_ne_zero
import Submission.Work.Cusp.wOf_add
import Submission.Work.Cusp.wOf_invY
import Submission.Work.Cusp.wedge_cover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

