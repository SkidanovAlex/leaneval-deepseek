import Mathlib
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Place.degree_eq_finrank
import Submission.Work.CurveBasics.Place.exists_place_of_valuationSubring

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Setup for the ramification index of the prime of `k[h]^int` attached to a place

This module contains the definitions and instances shared between the file
`Submission.Work.CurveBasics.Order.ramificationIdx_kxPrimeOfPlace` and the auxiliary lemmas
about it that are proved elsewhere in this workspace.
-/

namespace Work.CurveBasics.Order

open Work.CurveBasics
open scoped IntermediateField.algebraAdjoinAdjoin

noncomputable section

variable {k : Type*} [Field k]

/-- The valuation subring of the function field at a place is a discrete valuation ring. -/
instance instIsDiscreteValuationRingValuationSubring {C : Curve k} (Q : C.Place) :
    IsDiscreteValuationRing ↥(Q.valuationSubring) := by
  haveI : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Work.CurveBasics.Place.isDiscreteValuationRing Q
  change IsDiscreteValuationRing
    ↥(IsDedekindDomain.HeightOneSpectrum.valuation (↥C.functionField)
      (IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point))).valuationSubring
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsDiscreteValuationRing.equivValuationSubring (A := C.left.presheaf.stalk Q.point)
      (K := ↥C.functionField))

/-- The crux statement for `ramificationIdx_kxPrimeOfPlace`: the valuation subring at a place
where `h` vanishes is the localisation of the integral closure `k[h]^int` at the prime attached
to the place; equivalently, every element of the valuation subring is a quotient of integral
elements whose denominator does not lie in that prime. -/
def CruxStatement (C : Curve k) (h : C.functionField) (Q : C.Place)
    (hQ : 0 < C.ordAt h Q) : Prop :=
  ∀ x ∈ Q.valuationSubring, ∃ (s : ↥(C.ordClosure h)) (a : ↥(C.ordClosure h)),
    s ∉ kxPrimeOfPlace C h Q hQ.le ∧ (s : C.functionField) * x = (a : C.functionField)

/-- The base field `k(h)` inside the function field. -/
abbrev kxBase (C : Curve k) (h : C.functionField) :
    IntermediateField k C.functionField :=
  IntermediateField.adjoin k ({h} : Set C.functionField)

/-- The separable closure of `k(h)` in `K(C)`. -/
abbrev kxSep (C : Curve k) (h : C.functionField) :
    IntermediateField ↥(kxBase C h) C.functionField :=
  separableClosure ↥(kxBase C h) C.functionField

/-- The integral closure of `k[h]` in the separable closure of `k(h)`, as a type. -/
abbrev kxSepInt (C : Curve k) (h : C.functionField) : Type _ :=
  ↥(integralClosure (C.ordBase h) ↥(kxSep C h))

/-- The denominator property for the separable closure of `k(h)`: every element of the valuation
subring of `K(C)` at `Q` which lies in the separable closure of `k(h)` is a quotient of elements
integral over `k[h]`, with denominator a unit of the valuation ring. -/
def SepCaseStatement (C : Curve k) (h : C.functionField) (Q : C.Place)
    (hQ : 0 < C.ordAt h Q) : Prop :=
  ∀ y ∈ Q.valuationSubring, y ∈ (kxSep C h : Set C.functionField) →
    ∃ (s : kxSepInt C h) (a : kxSepInt C h) (u : (↥(Q.valuationSubring))ˣ),
      ((u : ↥(Q.valuationSubring)) : C.functionField) = (s : C.functionField) ∧
      (s : C.functionField) * y = (a : C.functionField)

end

end Work.CurveBasics.Order
