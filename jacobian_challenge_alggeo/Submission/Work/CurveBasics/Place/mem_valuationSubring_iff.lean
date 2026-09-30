/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The valuation subring at a place, and the order of vanishing

The local ring of a curve at a place `Q` is a discrete valuation ring, so the maximal ideal of
that local ring is a height-one prime and carries an adic valuation
`Q.valuation : K(C) → ℤᵐ⁰`, whose unit ball `Q.valuationSubring` is the subring of functions
regular at `Q`.  Mathlib's order of vanishing `Scheme.ord` at `Q` is (minus) the logarithm of
this same valuation, so a function is regular at `Q` exactly when its order of vanishing there
is nonnegative.
-/
import Mathlib
import Submission.Work.CurveBasics.Place.Valuation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics

namespace Curve

namespace Place

open scoped WithZero

/-- The order of vanishing of a function at a place is the negative of the logarithm of the
adic valuation attached to the place.  This is the bridge between Mathlib's
`AlgebraicGeometry.Scheme.ord` (built from `Ring.ordFrac` of the local ring) and the adic
valuation `Place.valuation` of the (discrete valuation) local ring. -/
lemma ord_eq_neg_log_valuation {k : Type*} [Field k] (C : Curve k) (Q : Curve.Place C)
    (x : C.functionField) :
    AlgebraicGeometry.Scheme.ord x Q.point = -(Q.valuation x).log := by
  by_cases hx : x = 0
  · subst hx
    simp [AlgebraicGeometry.Scheme.ord_zero]
  · rw [AlgebraicGeometry.Scheme.ord_eq_unzero_ordHom Q.eq_coheight_one hx,
      WithZero.toAdd_unzero_eq_log]
    have : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
      Q.instIsDiscreteValuationRing
    simp only [AlgebraicGeometry.Scheme.ordHom, Ring.ordFrac_eq_valuation_inv,
      WithZero.log_inv]
    rfl

end Place

end Curve

namespace Place

open Work.CurveBasics
open scoped WithZero

/-- For an element `v` of the value group `ℤᵐ⁰`, lying in the unit ball is equivalent to the
negated logarithm being nonnegative.  This is the pure value-group computation underlying
`Curve.Place.ord_eq_neg_log_valuation`. -/
private lemma le_one_iff_neg_log_nonneg (v : ℤᵐ⁰) : v ≤ 1 ↔ 0 ≤ -v.log := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [neg_nonneg, ← WithZero.exp_zero (M := ℤ), ← WithZero.log_le_iff_le_exp hv (a := 0)]

open Work.CurveBasics in
theorem mem_valuationSubring_iff {k : Type*} [Field k] (C : Curve k) (Q : C.Place)
    (x : C.functionField) :
    x ∈ Q.valuationSubring ↔ 0 ≤ AlgebraicGeometry.Scheme.ord x Q.point := by
  rw [Curve.Place.valuationSubring_eq, Valuation.mem_valuationSubring_iff Q.valuation x,
    Curve.Place.ord_eq_neg_log_valuation C Q x, le_one_iff_neg_log_nonneg]

end Place

end Work.CurveBasics
