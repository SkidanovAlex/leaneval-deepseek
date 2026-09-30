/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The valuation of a curve at a place

The local ring of a curve at a place is a discrete valuation ring, so a place determines a
valuation subring of `K(C)`: the subring of rational functions regular at the place.
-/
import Submission.Work.CurveBasics.Place.Coheight
import Submission.Work.CurveBasics.Place.isDiscreteValuationRing
import Submission.Work.CurveBasics.Order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

namespace Place

variable {C : Curve k}

/-- The local ring of a curve at a place is a discrete valuation ring. -/
theorem instIsDiscreteValuationRing (Q : Place C) :
    IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
  Work.CurveBasics.Place.isDiscreteValuationRing Q

/-- A place of a curve determines a nontrivial valuation subring of the function field:
the subring of functions regular at the place. -/
noncomputable def valuationSubring (Q : Place C) : ValuationSubring C.functionField :=
  haveI : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) := Q.instIsDiscreteValuationRing
  ((IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point)).valuation
    C.functionField).valuationSubring

/-- The valuation of the function field at a place, as a map to `ℤᵐ⁰`. -/
noncomputable def valuation (Q : Place C) :
    Valuation C.functionField (WithZero (Multiplicative ℤ)) :=
  haveI : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) := Q.instIsDiscreteValuationRing
  (IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point)).valuation C.functionField

/-- A uniformizer of the local ring of a curve at a place, viewed in the function field. -/
noncomputable def uniformizer (Q : Place C) : C.functionField :=
  haveI : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) := Q.instIsDiscreteValuationRing
  algebraMap (C.left.presheaf.stalk Q.point) C.functionField
    (Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal (C.left.presheaf.stalk Q.point)))

@[simp]
theorem valuationSubring_eq (Q : Place C) :
    Q.valuationSubring = Q.valuation.valuationSubring := rfl

end Place

end

end Curve

end Work.CurveBasics
