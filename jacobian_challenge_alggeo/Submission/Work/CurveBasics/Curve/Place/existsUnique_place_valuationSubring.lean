import Mathlib
import Submission.Work.CurveBasics.Place.exists_place_of_valuationSubring
import Submission.Work.CurveBasics.Place.place_eq_of_valuationSubring_eq
import Submission.Work.CurveBasics.Place.Valuation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveBasics.Curve.Place

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem existsUnique_place_valuationSubring {k : Type u} [Field k] (C : Curve k)
    (V : ValuationSubring C.functionField)
    (hV : ∀ c : k, algebraMap k C.functionField c ∈ V) (hne : V ≠ ⊤) :
    ∃! Q : Curve.Place C, V = Q.valuationSubring := by
  obtain ⟨Q, hQ⟩ :=
    Work.CurveBasics.Place.exists_place_of_valuationSubring C V hV hne
  refine ⟨Q, hQ, ?_⟩
  intro Q' hQ'
  exact Work.CurveBasics.Place.place_eq_of_valuationSubring_eq C (hQ'.symm.trans hQ)

end Work.CurveBasics.Curve.Place
