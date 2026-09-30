import Mathlib
import Submission.Work.GenusZero.Principal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.GenusZero.Principal

/-- **Linear equivalence at equal degree, genus zero**: on a curve of genus `0`, two divisors of
the same degree are linearly equivalent.  The difference `D - E` has degree `0`, so it is the
divisor of a nonzero rational function by `Work.GenusZero.principal_of_deg_zero`. -/
theorem linEquiv_of_deg_eq {k : Type u} [Field k] (C : CurveBasics.Curve k) (hg : RiemannRoch.Curve.genus C = 0) {D E : C.Div} (h : C.deg D = C.deg E) : ∃ h : C.functionField, h ≠ 0 ∧ C.div h = D - E := by
  refine Work.GenusZero.principal_of_deg_zero C hg (D - E) ?_
  rw [CurveBasics.Curve.deg_sub, h, sub_self]

end Work.GenusZero.Principal
