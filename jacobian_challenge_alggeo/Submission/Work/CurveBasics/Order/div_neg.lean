import Mathlib
import Submission.Work.CurveBasics.Order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The order of vanishing is invariant under negation

`Scheme.ord` is a monoid-with-zero homomorphism on the function field, so it is additive on
products of nonzero elements.  Writing `-h = (-1) * h` and observing that `ord (-1) = 0`
(because `(-1) * (-1) = 1` and `ord 1 = 0`), we get `ord (-h) = ord h` at every point, hence
`C.div (-h) = C.div h`.
-/

namespace Work.CurveBasics.Order

open Work.CurveBasics

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

/-- The order of vanishing of a rational function is unchanged by negation. -/
theorem ord_neg {k : Type*} [Field k] (C : Curve k) (h : C.functionField) (Q : C.Place) :
    Scheme.ord (-h) Q.point = Scheme.ord h Q.point := by
  rcases eq_or_ne h 0 with hh | hh
  · subst hh
    simp
  · have hone : (1 : C.functionField) ≠ 0 := one_ne_zero
    have hmone : (-1 : C.functionField) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    -- `ord 1 = 0`, since `ord 1 = ord (1 * 1) = ord 1 + ord 1`.
    have hord_one : Scheme.ord (1 : C.functionField) Q.point = 0 := by
      have h := Scheme.ord_mul (x := Q.point) (f := (1 : C.functionField)) (g := (1 : C.functionField))
        hone hone
      rw [mul_one] at h
      linarith
    -- `ord (-1) = 0`, since `ord ((-1) * (-1)) = ord 1` and `(-1) * (-1) = 1`.
    have hord_mone : Scheme.ord (-1 : C.functionField) Q.point = 0 := by
      have h := Scheme.ord_mul (x := Q.point) (f := (-1 : C.functionField)) (g := (-1 : C.functionField))
        hmone hmone
      have hsq : (-1 : C.functionField) * (-1) = 1 := by ring
      rw [hsq, hord_one] at h
      linarith
    have hneg : (-h : C.functionField) = (-1) * h := by ring
    rw [hneg, Scheme.ord_mul hmone hh, hord_mone, zero_add]

open Work.CurveBasics in
theorem div_neg {k : Type*} [Field k] (C : Curve k) (h : C.functionField) :
    C.div (-h) = C.div h := by
  ext Q
  rw [Curve.div_apply, Curve.div_apply]
  exact ord_neg C h Q

end Work.CurveBasics.Order
