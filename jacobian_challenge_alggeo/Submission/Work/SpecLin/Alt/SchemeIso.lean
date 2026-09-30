/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transport of the function field and of order of vanishing along an isomorphism of schemes

For an isomorphism `e : X ≅ Y` of irreducible schemes, the generic point of `X` maps to the
generic point of `Y` (an isomorphism is a homeomorphism, hence preserves the generic point).
Consequently `e` induces a ring homomorphism `ffMap e : K(Y) ⟶ K(X)` on function fields --
contravariantly, because the stalk map of `e.hom` goes from the stalk of `Y` to the stalk
of `X` -- which will be used to transport line bundles, divisors and linear equivalence
between base changes of a fixed curve along an isomorphism of fields.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace Work.SpecLin.Alt

variable {X Y : Scheme.{u}}

/-- An isomorphism of schemes is a homeomorphism, so it carries the generic point of its
source to the generic point of its target. -/
theorem iso_genericPoint [IrreducibleSpace X] [IrreducibleSpace Y] (e : X ≅ Y) :
    e.hom.base (genericPoint X) = genericPoint Y := by
  have hsurj : Function.Surjective e.hom.base := by
    intro y
    obtain ⟨x, hx⟩ := (Scheme.homeoOfIso e).surjective y
    exact ⟨x, by rw [← Scheme.homeoOfIso_apply e x]; exact hx⟩
  have hcont : Continuous e.hom.base := e.hom.continuous
  have hcl : closure ({e.hom.base (genericPoint X)} : Set Y) = Set.univ := by
    have h1 : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec _
    rw [← Set.image_singleton]
    have h2 : e.hom.base '' closure ({genericPoint X} : Set X) ⊆
        closure (e.hom.base '' {genericPoint X}) := image_closure_subset_closure_image hcont
    rw [h1, Set.image_univ, Set.range_eq_univ.mpr hsurj] at h2
    exact Set.eq_univ_of_univ_subset h2
  exact T0Space.t0 (inseparable_iff_specializes_and.mpr
    ⟨by rw [specializes_iff_mem_closure, hcl]; trivial,
     by rw [specializes_iff_mem_closure, genericPoint_spec]; trivial⟩)

/-- **The isomorphism of function fields induced by an isomorphism of schemes.**

`ffMap e : K(Y) ⟶ K(X)` is the stalk map of `e.hom` at the generic point of `X`, using that
`e.hom` carries `genericPoint X` to `genericPoint Y`. -/
noncomputable def ffMap [IrreducibleSpace X] [IrreducibleSpace Y] (e : X ≅ Y) :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (Inseparable.of_eq (iso_genericPoint e).symm)).hom ≫
    e.hom.stalkMap (genericPoint X)

end Work.SpecLin.Alt
