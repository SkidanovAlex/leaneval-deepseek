import Mathlib
import Submission.Work.CurveBasics.Divisor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Divisor

open Work.CurveBasics Work.CurveBasics.Curve in
theorem le_trans {k : Type*} [Field k] {C : Curve k} {D E F : C.Div}
    (h₁ : Div.le D E) (h₂ : Div.le E F) : Div.le D F := by
  rw [Div.le_iff] at h₁ h₂ ⊢
  intro Q
  linarith [h₁ Q, h₂ Q]

end Work.CurveBasics.Divisor
