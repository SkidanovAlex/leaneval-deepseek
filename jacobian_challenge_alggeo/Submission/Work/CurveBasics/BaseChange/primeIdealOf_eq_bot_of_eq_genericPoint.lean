import Mathlib
import Submission.Work.CurveBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.BaseChange

open Work.CurveBasics in
/-- If `xW` is a point of an affine open `W` of a curve whose image in the curve is the
generic point, then the prime ideal of `Γ(C, W)` attached to `xW` is the zero ideal. -/
theorem primeIdealOf_eq_bot_of_eq_genericPoint {k : Type*} [Field k] {C : Curve k}
    {W : C.left.Opens} (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] (xW : W)
    (h : (xW : C.left) = genericPoint C.left) :
    (hW.primeIdealOf xW).asIdeal = ⊥ := by
  have hx : xW = ⟨genericPoint C.left,
      ((genericPoint_spec C.left).mem_open_set_iff W.isOpen).mpr (by simpa using ‹Nonempty W›)⟩ :=
    Subtype.ext h
  rw [hx, hW.primeIdealOf_genericPoint, AlgebraicGeometry.genericPoint_eq_bot_of_affine]
  rfl

end Work.CurveBasics.BaseChange
