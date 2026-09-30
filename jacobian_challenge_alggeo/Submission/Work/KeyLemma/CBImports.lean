/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The slice of area `CB` (`Submission/Work/CurveBasics`) used by area `KL`

Area `KL` depends on the divisor theory, the places, and the base change of a curve from
area `CB`.  Rather than importing the whole of `CurveBasics.All` -- which changes under our
feet and currently contains modules that cannot be loaded -- this module lists the modules of
area `CB` that area `KL` actually depends on (the transitive closure of the modules that
provide `Curve`, `Curve.Place`, `Curve.Div`, `Curve.div`/`Curve.ordAt`, `Curve.baseChange`,
`Curve.divMap` and the pullback of divisors along a field extension).

Adding a dependency of area `KL` on area `CB` means adding a line here.
-/
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.BaseChange
import Submission.Work.CurveBasics.BaseChange.divMap_div
import Submission.Work.CurveBasics.BaseChange.divMap_isEffective
import Submission.Work.CurveBasics.BaseChange.exists_affine_nbhd
import Submission.Work.CurveBasics.BaseChange.exists_notMem_mul_mem_range
import Submission.Work.CurveBasics.BaseChange.functionFieldMap_algebraMap
import Submission.Work.CurveBasics.BaseChange.isAffineOpen_bcOpens
import Submission.Work.CurveBasics.BaseChange.isPullback_spec_affine
import Submission.Work.CurveBasics.BaseChange.krullDimLE_tensor
import Submission.Work.CurveBasics.BaseChange.krullDim_le_one
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff
import Submission.Work.CurveBasics.BaseChange.ordAt_fieldMap
import Submission.Work.CurveBasics.BaseChange.primeIdealOf_eq_bot_of_eq_genericPoint
import Submission.Work.CurveBasics.BaseChange.range_germ_baseChange
import Submission.Work.CurveBasics.BaseChangeDivisor
import Submission.Work.CurveBasics.BaseChangeFunctionField
import Submission.Work.CurveBasics.BaseChangeScheme
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Basic.Sections
import Submission.Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic
import Submission.Work.CurveBasics.Basic.isDomain_tensor_fractionRing
import Submission.Work.CurveBasics.Basic.isDomain_tensor_of_isOpenImmersion
import Submission.Work.CurveBasics.Basic.isDomain_tensor_sections
import Submission.Work.CurveBasics.Curve.LocalEquation
import Submission.Work.CurveBasics.Curve.exists_affine_principal
import Submission.Work.CurveBasics.Divisor
import Submission.Work.CurveBasics.Divisor.deg_eq_zero_iff
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.Linear.div_neg_of_not_regular
import Submission.Work.CurveBasics.Linear.finrank_quotient_add_place
import Submission.Work.CurveBasics.Linear.mul_mem_L_iff
import Submission.Work.CurveBasics.Order
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.PureConstantsAux
import Submission.Work.CurveBasics.Order.RamifIdxSetup
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.CurveBasics.Order.SumPrimesAux
import Submission.Work.CurveBasics.Order.deg_div
import Submission.Work.CurveBasics.Order.deg_div_split
import Submission.Work.CurveBasics.Order.div_algebraMap_eq_zero
import Submission.Work.CurveBasics.Order.div_inv
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField
import Submission.Work.CurveBasics.Order.finite_integralClosure_of_ringHom
import Submission.Work.CurveBasics.Order.finite_support_ord
import Submission.Work.CurveBasics.Order.integralClosure_adjoin_finite_general_assembly
import Submission.Work.CurveBasics.Order.isPurelyInseparable_of_ringEquiv_smul
import Submission.Work.CurveBasics.Order.kxClosure_finrank_general
import Submission.Work.CurveBasics.Order.kxClosure_residue_surjective
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_liesOver
import Submission.Work.CurveBasics.Order.kx_finite_of_embedding
import Submission.Work.CurveBasics.Order.kx_pure_insep
import Submission.Work.CurveBasics.Order.module_finite_integralClosure_of_ringEquiv
import Submission.Work.CurveBasics.Order.ordClosure_finite_general
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Order.ord_lem
import Submission.Work.CurveBasics.Order.perfectClosure_adjoin_gen
import Submission.Work.CurveBasics.Order.perfectClosure_separable_of_normal
import Submission.Work.CurveBasics.Order.ramificationIdx_eq_neg_log_valuation
import Submission.Work.CurveBasics.Order.ringEquivTransportAssembly
import Submission.Work.CurveBasics.Order.spso_inertiaDeg_eq
import Submission.Work.CurveBasics.Order.sum_ord_neg_eq_finrank
import Submission.Work.CurveBasics.Order.sum_primesOver_eq_sum_ord
import Submission.Work.CurveBasics.Order.valuationSubring_eq_atPrime
import Submission.Work.CurveBasics.Order.valuation_eq_of_surjective_of_valuationSubring_eq
import Submission.Work.CurveBasics.Place
import Submission.Work.CurveBasics.Place.Coheight
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.Place.degree_eq_finrank
import Submission.Work.CurveBasics.Place.exists_place_of_valuationSubring
import Submission.Work.CurveBasics.Place.isDiscreteValuationRing
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Place.ord_uniformizer
import Submission.Work.CurveBasics.Place.place_eq_of_valuationSubring_eq
import Submission.Work.CurveBasics.Place.residueDegree_pos
import Submission.Work.CurveBasics.Point.coheight_eq_one_of_isClosed
import Submission.Work.CurveBasics.Point.isClosed_of_coheight_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

