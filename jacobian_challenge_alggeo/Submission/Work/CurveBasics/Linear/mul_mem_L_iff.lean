import Mathlib
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.Order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Linear

open Work.CurveBasics in
theorem mul_mem_L_iff {k : Type*} [Field k] (C : Curve k) {D : C.Div} {h h' : C.functionField}
    (hh : h ≠ 0) (hh' : h' ≠ 0) :
    h * h' ∈ C.L (D - C.div h) ↔ h' ∈ C.L D := by
  rw [Curve.mem_L_iff, Curve.mem_L_iff]
  have hh'' : h * h' ≠ 0 := mul_ne_zero hh hh'
  -- The two divisors defining the two Riemann-Roch spaces agree.
  have hdiv : C.div (h * h') + (D - C.div h) = C.div h' + D := by
    rw [C.div_mul hh hh']; abel
  constructor
  · rintro (h0 | heff)
    · exact absurd h0 hh''
    · exact Or.inr (hdiv ▸ heff)
  · rintro (h0 | heff)
    · exact absurd h0 hh'
    · exact Or.inr (hdiv ▸ heff)

end Work.CurveBasics.Linear
