import Mathlib
import Submission.Work.CurveBasics.Order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The divisor of a constant is zero

The `k`-algebra structure on the function field `K(C)` of a curve `C` is the composite

`k ⟶ Γ(Spec k, ⊤) ⟶ Γ(C, ⊤) ⟶ K(C)`,

where the last map is `germToFunctionField ⊤`.  Hence the image of `c : k` in `K(C)` is the germ
of the section `φ c ∈ Γ(C, ⊤)`, where `φ = ΓSpecIso.inv ≫ C.hom.appTop`.  For `c ≠ 0` this
section is a unit (it is the image of the unit `c`), and the order of vanishing of the germ of a
unit section at any point is zero (`Scheme.ord_of_isUnit`).  Consequently the principal divisor
of a constant is zero: constants are never zeros or poles of a rational function.
-/

namespace Work.CurveBasics.Order

open Work.CurveBasics

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

/-- The order of vanishing of the image of `c : k` in the function field of a curve is zero at
every place: constants have neither zeros nor poles. -/
theorem ordAt_algebraMap_eq_zero {k : Type*} [Field k] (C : Curve k) (c : k) (Q : C.Place) :
    C.ordAt (algebraMap k C.functionField c) Q = 0 := by
  have htop : Nonempty (⊤ : C.left.Opens) := ⟨⟨genericPoint C.left, trivial⟩⟩
  -- Unfold the `k`-algebra structure: the image of `c` is the germ of the section `φ c`.
  have key : algebraMap k C.functionField c
      = C.left.germToFunctionField ⊤
          (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  rw [key]
  rcases eq_or_ne c 0 with hc | hc
  · -- The zero constant has order zero.
    subst hc
    simp only [map_zero]
    show Scheme.ord (0 : C.functionField) Q.point = 0
    simp
  · -- A nonzero constant is the germ of a unit, hence has order zero.
    refine Scheme.ord_of_isUnit ?_ trivial
    exact ((isUnit_iff_ne_zero.mpr hc).map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom).map
      (C.hom.appTop).hom

open Work.CurveBasics in
theorem div_algebraMap_eq_zero {k : Type*} [Field k] (C : Curve k) (c : k) :
    C.div (algebraMap k C.functionField c) = 0 := by
  ext Q
  rw [Curve.div_apply]
  exact ordAt_algebraMap_eq_zero C c Q

end Work.CurveBasics.Order
