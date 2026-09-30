import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap_of_not_isClosed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem divMap_div {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') {f : C.functionField} (hf : f ≠ 0) :
    S.divMap (C.div f) = C'.div (S.fieldMap.hom f) := by
  classical
  ext Q'
  rw [divMap_apply, Curve.div_apply]
  by_cases hc : IsClosed ({S.π Q'.point} : Set C.left)
  · rw [divMapCoeff, dif_pos hc, Curve.div_apply]
    show C.ordAt f (S.under Q' hc) * S.ramIdx Q' = C'.ordAt (S.fieldMap.hom f) Q'
    rw [ordAt_fieldMap S Q' hc hf]
    ring
  · rw [divMapCoeff, dif_neg hc]
    show 0 = C'.ordAt (S.fieldMap.hom f) Q'
    rw [ordAt_fieldMap_of_not_isClosed S Q' hc hf]

end Work.CurveBasics.Curve.BCSquare
