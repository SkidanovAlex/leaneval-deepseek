import Mathlib
import Submission.Work.CurveBasics.BCSquare

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
/-- The map of function fields `K(C) ⟶ K(C')` induced by a base-change square is injective.

This holds simply because `K(C)` is a field: a ring homomorphism whose source is a field is
injective. -/
theorem fieldMap_injective {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') :
    Function.Injective S.fieldMap.hom := by
  intro a b hab
  by_contra hne
  have h1 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h2 : S.fieldMap.hom (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h3 : (1 : C'.functionField) = 0 := by
    have hm := map_mul S.fieldMap.hom (a - b) (a - b)⁻¹
    rw [mul_inv_cancel₀ h1, map_one, h2, zero_mul] at hm
    exact hm
  exact one_ne_zero h3

end Work.CurveBasics.Curve.BCSquare
