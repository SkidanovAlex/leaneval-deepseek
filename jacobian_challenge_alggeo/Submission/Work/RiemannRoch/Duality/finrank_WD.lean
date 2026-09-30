import Mathlib
import Submission.Work.RiemannRoch.Differentials
import Submission.Work.RiemannRoch.RRLib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

namespace Work.RiemannRoch.Duality

open Work.RiemannRoch

/-- `WD D` is the dual of the quotient `H1 C D = A/(K + A(D))`, so its `k`-dimension is `i D`.
The equality of `finrank`s is unconditional: both sides are `0` for an infinite-dimensional
quotient. -/
theorem finrank_WD {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) (D : C.Div) :
    Module.finrank k ↥(Work.RiemannRoch.Curve.WD C D) = Work.RiemannRoch.Curve.i C D := by
  rw [← (Work.RiemannRoch.Curve.WDequiv C D).finrank_eq, Subspace.dual_finrank_eq]
  exact rfl

end Work.RiemannRoch.Duality
