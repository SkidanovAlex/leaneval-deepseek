import Mathlib
import Submission.Work.RiemannRoch.Pole
import Submission.Work.CurveBasics.exists_separating_element

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.RiemannRoch.Pole

/-- The function field of a smooth, proper, geometrically irreducible curve over a field has a
transcendental element (the uniformizer at any place). -/
theorem exists_transcendental {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) :
    ∃ x : C.functionField, Transcendental k x :=
  Work.CurveBasics.exists_transcendental C

end Work.RiemannRoch.Pole
