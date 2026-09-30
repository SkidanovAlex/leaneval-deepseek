import Mathlib
import Submission.Work.CurveBasics.Order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

/-- The order of vanishing of the constant function `1` at any point is zero. -/
theorem ord_one {k : Type*} [Field k] (C : Curve k) (Q : C.Place) :
    AlgebraicGeometry.Scheme.ord (1 : C.functionField) Q.point = 0 := by
  by_cases hq : Order.coheight Q.point = 1
  · rw [AlgebraicGeometry.Scheme.ord_eq_ordHom_of_coheight_eq_one hq]; simp
  · simp [AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hq]

/-- The order of vanishing of the inverse of a rational function is the negative of its order. -/
theorem ordAt_inv {k : Type*} [Field k] (C : Curve k) {h : C.functionField} (hh : h ≠ 0)
    (Q : C.Place) :
    AlgebraicGeometry.Scheme.ord h⁻¹ Q.point = -AlgebraicGeometry.Scheme.ord h Q.point := by
  have h1 : AlgebraicGeometry.Scheme.ord (h⁻¹ * h) Q.point =
      AlgebraicGeometry.Scheme.ord h⁻¹ Q.point +
        AlgebraicGeometry.Scheme.ord h Q.point :=
    AlgebraicGeometry.Scheme.ord_mul (inv_ne_zero hh) hh
  rw [inv_mul_cancel₀ hh] at h1
  have h2 : AlgebraicGeometry.Scheme.ord (1 : C.functionField) Q.point = 0 := ord_one C Q
  linarith

open Work.CurveBasics in
theorem div_inv {k : Type*} [Field k] (C : Curve k) {h : C.functionField} (hh : h ≠ 0) :
    C.div h⁻¹ = -C.div h := by
  ext Q
  simp only [Curve.div_apply, Finsupp.neg_apply]
  exact ordAt_inv C hh Q

end Work.CurveBasics.Order
