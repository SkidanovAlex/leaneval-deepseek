import Mathlib
import Submission.Work.RiemannRoch.Pole
import Submission.Work.CurveBasics.Order.deg_div
import Submission.Work.CurveBasics.Divisor.deg_nonneg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

namespace Work.RiemannRoch.RR

open Work.CurveBasics

/-- **The Riemann-Roch space of a negative-degree divisor is zero.**

If `f ≠ 0` lies in `L D`, then `div f + D` is effective, hence has nonnegative degree; but its
degree is `deg (div f) + deg D = deg D < 0`, a contradiction.  The only input is that the
principal divisor of a rational function has degree zero
(`Work.CurveBasics.Order.deg_div`). -/
theorem L_eq_bot_of_deg_neg {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D : C.Div}
    (h : C.deg D < 0) : C.L D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [C.mem_L_iff] at hf
  rcases hf with h0 | hf
  · exact h0
  · exfalso
    have h1 : 0 ≤ C.deg (C.div f + D) := Work.CurveBasics.Divisor.deg_nonneg hf
    rw [C.deg_add, Work.CurveBasics.Order.deg_div C f] at h1
    linarith

end Work.RiemannRoch.RR
