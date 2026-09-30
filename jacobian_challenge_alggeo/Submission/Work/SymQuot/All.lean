/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area SY — finite-group quotients and symmetric powers: the exported API

Import this module to get the whole `SymQuot` chapter:

* `Submission.Work.SymQuot.Basic` — group actions on schemes, invariant opens, the cover data
  used to build quotients;
* `Submission.Work.SymQuot.Sections` — the action of `G` on the sections `Γ(X, U)` over a
  `G`-invariant open `U`, and the subring `Γ(X,U)^G` of invariants;
* `Submission.Work.SymQuot.Invariants` — invariant rings: the universal property, base change
  and localization, integrality, surjectivity of `Spec B ⟶ Spec B^G`;
* `Submission.Work.SymQuot.Chart` — the chart `Spec Γ(X,U)^G` of an invariant affine open, the
  chart map `U ⟶ chart U` and the restriction maps between charts, together with the delegated
  geometric leaves (`Chart/…`): the fibres of the chart map are the orbits, the images of two
  charts meet in the chart of the intersection, `chartRes` is an open immersion, and the chart is a
  categorical quotient for arbitrary targets;
* `Submission.Work.SymQuot.QuotientData`, `… .Quotient`, `… .QuotientMap`, `… .QuotientHom` — the
  quotient `X/Γ` as a locally directed colimit of the charts, the quotient map `X ⟶ X/Γ`, its
  categorical quotient property and the structure morphism over a base;
* `Submission.Work.SymQuot.Product`, `… .SymAction` — powers `X^n`, the `S_n`-action on them by
  permutation of the factors (the first input of `Sym^n C = (C^n)/S_n`).

The remaining layer (the `QuotientData` instance for `C^n` with the `S_n`-action, hence `Sym^n C`
itself, and the point/divisor dictionary) is described in `Submission/Work/SymQuot/NOTES.md`,
together with the precise statement that is left to prove.
-/
import Submission.Work.SymQuot.Basic
import Submission.Work.SymQuot.Sections
import Submission.Work.SymQuot.Invariants
import Submission.Work.SymQuot.Invariants.fixedPoints_isIntegral
import Submission.Work.SymQuot.Invariants.finiteType_fixedPoints
import Submission.Work.SymQuot.Invariants.tensor_fixedPoints
import Submission.Work.SymQuot.Invariants.fixedPoints_isLocalization_of_isLocalization
import Submission.Work.SymQuot.Invariants.fixedPoints_isInvariant
import Submission.Work.SymQuot.Invariants.fixedPoints_isLocalization_away
import Submission.Work.SymQuot.Invariants.fixedPoints_lift
import Submission.Work.SymQuot.Invariants.surjective_specMap_fixedPoints
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Chart.chartRes_chartMap
import Submission.Work.SymQuot.Chart.chartRes_isOpenImmersion
import Submission.Work.SymQuot.Chart.chartRes_isOpenImmersion_alt
import Submission.Work.SymQuot.Chart.chartRes_pullback_iso
import Submission.Work.SymQuot.Chart.chartMap_fiber_orbit
import Submission.Work.SymQuot.Chart.chartMap_image_inf
import Submission.Work.SymQuot.Chart.chartFunctor_isLocallyDirected
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.Chart.chartRes_isEmbedding
import Submission.Work.SymQuot.Chart.chartRes_cover
import Submission.Work.SymQuot.Chart.chartRes_isOpen_range
import Submission.Work.SymQuot.Chart.isAffineOpen_inf_of_le
import Submission.Work.SymQuot.UnitsPreimage
import Submission.Work.SymQuot.Chart.quotient_desc
import Submission.Work.SymQuot.Chart.exists_quotientMap
import Submission.Work.SymQuot.Chart.exists_chart_factor
import Submission.Work.SymQuot.QuotientMap
import Submission.Work.SymQuot.Chart.quotient_lift
import Submission.Work.SymQuot.QuotientHom
import Submission.Work.SymQuot.Product
import Submission.Work.SymQuot.Product.permIso_mul
import Submission.Work.SymQuot.Product.permIso_hom_proj
import Submission.Work.SymQuot.Product.permIso_one
import Submission.Work.SymQuot.SymAction
import Submission.Work.SymQuot.Chart.quotientMap_isIntegralHom
import Submission.Work.SymQuot.CurveInput
import Submission.Work.SymQuot.CurveInstance
import Submission.Work.SymQuot.ProdOpen
import Submission.Work.SymQuot.Prod.isSeparated_prod
import Submission.Work.SymQuot.Prod.isProper_prod
import Submission.Work.SymQuot.Prod.isAffineOpen_piOpen
import Submission.Work.SymQuot.SymData
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Sym.sym_one
import Submission.Work.SymQuot.Sym.isIntegral_sym
import Submission.Work.SymQuot.Sym.geometricallyIrreducible_sym
import Submission.Work.SymQuot.Sym.quasiCompact_sym
import Submission.Work.SymQuot.Sym.isProper_sym
import Submission.Work.SymQuot.Sym.locallyOfFiniteType_sym
import Submission.Work.SymQuot.Sym.exists_powMap_eq
import Submission.Work.SymQuot.Sym.powMap_eq_iff_exists_perm
import Submission.Work.SymQuot.Chart.isFinite_quotientMap
import Submission.Work.SymQuot.Sym.FiniteChart
import Submission.Work.SymQuot.Sym.isFinite_quot
import Submission.Work.SymQuot.Sym.exists_finite_lift
import Submission.Work.SymQuot.Sym.isSeparated_sym
import Submission.Work.SymQuot.DivOf.Setup
import Submission.Work.SymQuot.DivOf.SymChart
import Submission.Work.SymQuot.DivOf.ChartPt
import Submission.Work.SymQuot.DivOf.AffineCurve
import Submission.Work.SymQuot.DivOf.chartPt_exists
import Submission.Work.SymQuot.DivOf.chartPt_eval_eq
import Submission.Work.SymQuot.DivOf.localIdealSet_isIdeal
import Submission.Work.SymQuot.DivOf.isDedekindDomain_sections
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.exists_bcSquare_baseChange
import Submission.Work.SymQuot.DivOf.localIdealSet_mem_iff
import Submission.Work.SymQuot.DivOf.le_placeOrder_iff
import Submission.Work.SymQuot.DivOf.placeIdeal_injective
import Submission.Work.SymQuot.DivOf.heightOneSpectrum_equiv_place
import Submission.Work.SymQuot.DivOf.IdealData
import Submission.Work.SymQuot.DivOf.DivisorOfIdeal
import Submission.Work.SymQuot.DivOf.CharIdeal
import Submission.Work.SymQuot.DivOf.GenCharpoly
import Submission.Work.SymQuot.DivOf.CharIdealGen
import Submission.Work.SymQuot.DivOf.CharIdealGenDefs
import Submission.Work.SymQuot.DivOf.TowerSquare
import Submission.Work.SymQuot.DivOf.divMap_injective
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_mul
import Submission.Work.SymQuot.DivOf.genCharpoly_coeff_coeff_mem
import Submission.Work.SymQuot.DivOf.mem_placeIdeal_valAt_sub
import Submission.Work.SymQuot.DivOf.notMem_iUnion_intermediateField
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SymQuot.DivOf.exists_chartPt_nonempty
import Submission.Work.SymQuot.DivOf.card_symStab
import Submission.Work.SymQuot.DivOf.isDomain_piOpen_sections
import Submission.Work.SymQuot.DivOf.symAction_invariant_piOpen

import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.SymQuot.DivOf.SecAlpha
import Submission.Work.SymQuot.DivOf.bcSec_secAlpha
import Submission.Work.SymQuot.DivOf.bcSec_secConst
import Submission.Work.SymQuot.DivOf.lift_mem_V
import Submission.Work.SymQuot.DivOf.ptPlace_mem_bcOpens
import Submission.Work.SymQuot.DivOf.secAlpha_sub_mem_placeIdeal
import Submission.Work.SymQuot.DivOf.placeOrder_prod_placeIdeal
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_placeIdeal
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_prod_placeIdeal
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_injective
import Submission.Work.SymQuot.DivOf.eq_of_le_of_forall_placeOrder_le
import Submission.Work.SymQuot.DivOf.genGenerator_map_eq
import Submission.Work.SymQuot.DivOf.exists_eq_sum_secAlpha
import Submission.Work.SymQuot.DivOf.charIdeal_le_charIdealGen
import Submission.Work.SymQuot.DivOf.divMap_self
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_map_bcSec
import Submission.Work.SymQuot.DivOf.divMap_divOfChart
import Submission.Work.SymQuot.DivOf.divOf_deg
import Submission.Work.SymQuot.DivBaseInst
import Submission.Work.SymQuot.NormPoint.Basic
import Submission.Work.SymQuot.NormPoint.detT_eq_zero_of_swap_fixed
import Submission.Work.SymQuot.NormPoint.detT_mul
import Submission.Work.SymQuot.NormPoint.normVal_eq_evalT
import Submission.Work.SymQuot.NormPoint.exists_gen_mod_mul
import Submission.Work.SymQuot.NormPoint.exists_flagBasis
import Submission.Work.SymQuot.DivOf.divOf_powMapC1
import Submission.Work.SymQuot.DivOf.divOf_powMap
import Submission.Work.SymQuot.DivOf.ptDiv_sum_eq_iff
import Submission.Work.SymQuot.DivOf.divOf_injective
import Submission.Work.SymQuot.DivOf.divOf_map
import Submission.Work.SymQuot.NormPoint.NormPoint
import Submission.Work.SymQuot.NormPoint.bcT_exists
import Submission.Work.SymQuot.NormPoint.BaseChange
import Submission.Work.SymQuot.NormPoint.normVal_basis_indep
import Submission.Work.SymQuot.DivOf.Complete.Setup
import Submission.Work.SymQuot.DivOf.Complete.ptOfAlgHom_mem
import Submission.Work.SymQuot.DivOf.Complete.RPt_map_ptOfAlgHom
import Submission.Work.SymQuot.DivOf.Complete.idealOfDiv_ne_bot
import Submission.Work.SymQuot.DivOf.Complete.divisorOfIdeal_idealOfDiv
import Submission.Work.SymQuot.DivOf.Complete.exists_affine_of_div
import Submission.Work.SymQuot.NormPoint.bcT_mem_symTensors
import Submission.Work.SymQuot.NormPoint.normVal_bcT
import Submission.Work.SymQuot.DivOf.Complete.evalAlg_coordPullbackAt
import Submission.Work.SymQuot.DivOf.Complete.evalAlg_comp
import Submission.Work.SymQuot.DivOf.Complete.evalAlg_perm_of_mem
import Submission.Work.SymQuot.DivOf.Complete.chartIota_comp_hom
import Submission.Work.SymQuot.DivOf.Complete.PtOfChartHom
import Submission.Work.SymQuot.DivOf.Complete.exists_ptDiv_sum_of_div
import Submission.Work.SymQuot.DivOf.Complete.ptOfChartHom_evalAlg
import Submission.Work.SymQuot.DivOf.Complete.ptVal_ptOfAlgHom
import Submission.Work.SymQuot.SymGeomOfComplete
import Submission.Work.SymQuot.Invariants.tensor_fixedPoints_of_flat
import Submission.Work.SymQuot.RelQuot.Setup
import Submission.Work.SymQuot.RelQuot.relQuot

import Submission.Work.SymQuot.DivOf.Complete.divOf_complete
import Submission.Work.SymQuot.DivOf.Complete.tensorQuotEquiv_bcSec
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.SymProps
import Submission.Work.SymQuot.RelQuot.exists_addMap
import Submission.Work.SymQuot.AddMap
import Submission.Work.SymQuot.CurveIso
import Submission.Work.SymQuot.Sym.curveIso_divOf
import Submission.Work.SymQuot.Sym.curveIso_isIso
import Submission.Work.SymQuot.Sym.symGeom_zero
import Submission.Work.SymQuot.Sym.geometricallyIntegral_sym
import Submission.Work.SymQuot.OfDiv
import Submission.Work.SymQuot.OfDiv.addMap_divOf
import Submission.Work.SymQuot.OfDiv.constMap_divOf

import Submission.Work.SymQuot.OfDiv.curveAdd_divOf
import Submission.Work.SymQuot.OfDiv.addMap_divOf_zero_left
import Submission.Work.SymQuot.OfDiv.addMap_divOf_zero_right
import Submission.Work.SymQuot.OfDiv.constMapZero_divOf

import Submission.Work.SymQuot.BaseChange.exists_symBaseChangeIso

import Submission.Work.SymQuot.BaseChange.ptsBaseChange

import Submission.Work.SymQuot.BaseChange.PowMapBeta

import Submission.Work.SymQuot.BaseChange.powMap_symBeta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


-- Remaining: the rest of the `DivOf` construction (`divOf`, `SymGeom`, `SymBC`) — see NOTES.md.
--
-- NOT imported (abandoned route, kept for the record): `DivOf/Ring.lean`,
-- `DivOf/chartInvariants_le_subgroupInvariants.lean`,
-- `DivOf/coordMap_mem_subgroupInvariants.lean`.  These build the fibre ring `A' ⊗_A F` of the
-- `S_{n-1}`-invariants, which is **not** the ring of the divisor: its `F`-dimension drops to
-- `Σ_{z ∈ Supp D} [κ(z):F] < n` at non-reduced divisors, so `divOf` cannot be extracted from it.
-- See the "SESSION 3" section of NOTES.md for the corrected construction.
