/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CB — curve basics: the exported API

Import this module to get the whole curve-basics chapter:

* `Work.CurveBasics.Curve` — the bundle of a smooth, proper, geometrically irreducible
  curve over a field, with all its instances;
* `Work.CurveBasics.Curve.Place` — closed points, their local rings (discrete valuation
  rings), residue fields, degrees and valuation subrings of `K(C)`;
* `Work.CurveBasics.Curve.Div`, `Curve.deg` — divisors and their degree;
* `Work.CurveBasics.Curve.div` — the principal divisor of a rational function;
* `Work.CurveBasics.Curve.L`, `Curve.l` — Riemann–Roch spaces;
* `Work.CurveBasics.Curve.baseChange` — base change along a field extension.
-/
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Basic.Sections
import Submission.Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic
import Submission.Work.CurveBasics.Place
import Submission.Work.CurveBasics.Place.Coheight
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.Place.isDiscreteValuationRing
import Submission.Work.CurveBasics.Place.residueDegree_pos
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Place.degree_eq_finrank
import Submission.Work.CurveBasics.Place.ord_uniformizer
import Submission.Work.CurveBasics.Point.isClosed_of_coheight_eq_one
import Submission.Work.CurveBasics.Point.coheight_eq_one_of_isClosed
import Submission.Work.CurveBasics.Divisor
import Submission.Work.CurveBasics.Divisor.le_trans
import Submission.Work.CurveBasics.Divisor.le_antisymm
import Submission.Work.CurveBasics.Divisor.deg_nonneg
import Submission.Work.CurveBasics.Divisor.deg_eq_zero_iff
import Submission.Work.CurveBasics.Order
import Submission.Work.CurveBasics.Order.finite_support_ord
import Submission.Work.CurveBasics.Order.div_algebraMap_eq_zero
import Submission.Work.CurveBasics.Order.div_neg
import Submission.Work.CurveBasics.Order.div_inv
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.Linear.mul_mem_L_iff
import Submission.Work.CurveBasics.BaseChangeFunctionField
import Submission.Work.CurveBasics.BaseChange.exists_affine_nbhd
import Submission.Work.CurveBasics.BaseChange.isAffineOpen_bcOpens
import Submission.Work.CurveBasics.BaseChange.functionFieldMap_algebraMap
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff
import Submission.Work.CurveBasics.BaseChange.range_germ_baseChange
import Submission.Work.CurveBasics.BaseChangeDivisor
import Submission.Work.CurveBasics.BaseChange.divMap_isEffective
import Submission.Work.CurveBasics.BaseChange.divMap_div
import Submission.Work.CurveBasics.BaseChange.ordAt_fieldMap
import Submission.Work.CurveBasics.BaseChangeScheme
import Submission.Work.CurveBasics.BaseChange

import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Curve.exists_affine_principal
import Submission.Work.CurveBasics.Curve.L_eq_iInter_mul_range
import Submission.Work.CurveBasics.Curve.LocalEquation
import Submission.Work.CurveBasics.Curve.Place.existsUnique_place_valuationSubring
import Submission.Work.CurveBasics.Place.exists_place_of_valuationSubring
import Submission.Work.CurveBasics.Place.place_eq_of_valuationSubring_eq
import Submission.Work.CurveBasics.Order.deg_div
import Submission.Work.CurveBasics.Linear.finrank_quotient_add_place
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_algebraMap
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_injective
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap_of_not_isClosed
import Submission.Work.CurveBasics.Curve.BCSquare.divMap_isEffective
import Submission.Work.CurveBasics.Curve.BCSquare.divMap_div
import Submission.Work.CurveBasics.Curve.BCSquare.divMap_mono
import Submission.Work.CurveBasics.Curve.BCSquare.divMap_comp
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_comp
import Submission.Work.CurveBasics.Curve.BCSquare.L_divMap_local
import Submission.Work.CurveBasics.Curve.BCSquare.range_germ_baseChange
import Submission.Work.CurveBasics.Curve.BCSquare.linearIndependent_fieldMap
import Submission.Work.CurveBasics.Curve.BCSquare.L_divMap
import Submission.Work.CurveBasics.Curve.BCSquare.l_divMap
import Submission.Work.CurveBasics.Curve.BCSquare.linEquiv_divMap_iff
import Submission.Work.CurveBasics.Curve.BCSquare.span_iInf
import Submission.Work.CurveBasics.Curve.exists_finite_affine_cover_with_equations

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

