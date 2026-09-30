import Mathlib
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Place.degree_eq_finrank
import Submission.Work.CurveBasics.Order.inertiaDeg_kxPrimeOfPlace_eq_finrank

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveBasics.Order

open Work.CurveBasics

open Work.CurveBasics in
/-- The inertia degree of the prime of `k[x]^int` at a place where `x` vanishes is the residue
degree of the place. -/
theorem inertiaDeg_eq_residueDegree {k : Type*} [Field k] (C : Curve k) (x : C.functionField)
    (hx : Transcendental k x) (Q : C.Place) (hQ : 0 < C.ordAt x Q) :
    ((kxPrimeOfPlace C x Q hQ.le).inertiaDeg ↥(Algebra.adjoin k ({x} : Set C.functionField)) : ℤ)
      = (C.hom.residueDegree Q.point : ℤ) := by
  rw [inertiaDeg_kxPrimeOfPlace_eq_finrank C x hx Q hQ, ← Place.degree_eq_finrank Q]

end Work.CurveBasics.Order
