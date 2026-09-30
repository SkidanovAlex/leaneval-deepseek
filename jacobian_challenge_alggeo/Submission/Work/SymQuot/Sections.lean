/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The action of a group on the sections over an invariant open (area SY)

Given an action of a group `G` on a scheme `X` (`Work.SymQuot.GAction`) and a `G`-invariant open
subscheme `U ⊆ X`, the group acts on the ring `Γ(X, U)` of sections over `U`.  The invariants of
this action are the local building blocks of the quotient `X/G`.
-/
import Submission.Work.SymQuot.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

/-- A congruence for `Scheme.Hom.appLE` in the morphism: if `f = g` then the induced maps on
sections agree. -/
lemma appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    Scheme.Hom.appLE f U V e = Scheme.Hom.appLE g U V e' := by
  cases h
  simp only [Scheme.Hom.appLE]

/-- `appLE` is insensitive to the proof of the inclusion. -/
lemma appLE_congr_le {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e e' : V ≤ f ⁻¹ᵁ U) : Scheme.Hom.appLE f U V e = Scheme.Hom.appLE f U V e' := by
  simp only [Scheme.Hom.appLE]

/-- The identity morphism induces the identity on sections. -/
lemma appLE_id {X : Scheme.{u}} (U : X.Opens) (e : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) :
    Scheme.Hom.appLE (𝟙 X : X ⟶ X) U U e = 𝟙 Γ(X, U) := by
  rw [← appLE_congr_le (𝟙 X : X ⟶ X) (le_rfl : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) e]
  change Scheme.Hom.appLE (𝟙 X : X ⟶ X) U ((𝟙 X : X ⟶ X) ⁻¹ᵁ U) le_rfl = 𝟙 Γ(X, U)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]

namespace GAction

variable {G : Type u} [Group G] {X : Scheme.{u}} (A : GAction G X)

/-- The ring homomorphism `Γ(X, U) → Γ(X, U)` induced by `g : G` on the sections over a
`G`-invariant open `U`. -/
def sectionHom (U : X.Opens) (hU : A.IsInvariantOpen U) (g : G) : Γ(X, U) →+* Γ(X, U) :=
  (Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm)).hom

@[simp]
lemma sectionHom_apply (U : X.Opens) (hU : A.IsInvariantOpen U) (g : G) (s : Γ(X, U)) :
    sectionHom A U hU g s =
      Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm) s := rfl

@[simp]
lemma sectionHom_one (U : X.Opens) (hU : A.IsInvariantOpen U) :
    sectionHom A U hU 1 = RingHom.id Γ(X, U) := by
  ext s
  simp only [sectionHom_apply, RingHom.id_apply]
  rw [appLE_congr_hom (f := A.hom 1) (g := 𝟙 X) (U := U) (V := U) A.hom_one
    (le_of_eq (hU 1).symm) (le_of_eq rfl)]
  rw [appLE_id]
  rfl

@[simp]
lemma sectionHom_mul (U : X.Opens) (hU : A.IsInvariantOpen U) (g h : G) :
    sectionHom A U hU (g * h) = (sectionHom A U hU h).comp (sectionHom A U hU g) := by
  ext s
  simp only [sectionHom_apply, RingHom.comp_apply]
  rw [appLE_congr_hom (f := A.hom (g * h)) (g := A.hom h ≫ A.hom g) (U := U) (V := U)
    (A.hom_mul g h) _ _]
  rw [← Scheme.Hom.appLE_comp_appLE (A.hom h) (A.hom g) U U U
      (le_of_eq (hU g).symm) (le_of_eq (hU h).symm)]
  rw [ConcreteCategory.comp_apply]
  all_goals first
    | rfl
    | rw [Scheme.Hom.comp_preimage, hU g, hU h]

/-- The action of `G` on the sections `Γ(X, U)` over a `G`-invariant open `U`. -/
@[reducible]
def sectionMulSemiringAction (U : X.Opens) (hU : A.IsInvariantOpen U) :
    MulSemiringAction G Γ(X, U) where
  smul g := sectionHom A U hU g⁻¹
  one_smul s := by
    show sectionHom A U hU 1⁻¹ s = s
    simp
  mul_smul g h s := by
    show sectionHom A U hU (g * h)⁻¹ s =
      sectionHom A U hU g⁻¹ (sectionHom A U hU h⁻¹ s)
    simp only [mul_inv_rev, sectionHom_mul, RingHom.comp_apply]
  smul_zero g := map_zero (sectionHom A U hU g⁻¹)
  smul_add g s t := map_add (sectionHom A U hU g⁻¹) s t
  smul_one g := map_one (sectionHom A U hU g⁻¹)
  smul_mul g s t := map_mul (sectionHom A U hU g⁻¹) s t

/-- The ring of invariants of the action of `G` on the sections over a `G`-invariant open,
with respect to an action instance on the sections (normally
`A.sectionMulSemiringAction U hU`, installed locally with `letI`). -/
abbrev sectionInvariants (U : X.Opens) [MulSemiringAction G Γ(X, U)] : Subring Γ(X, U) :=
  FixedPoints.subring Γ(X, U) G

/-- The subalgebra of invariants of the action of `G` on the sections over a `G`-invariant open,
with respect to an action instance on the sections. -/
abbrev sectionInvariantsAlgebra (U : X.Opens) (A' : Type u) [CommRing A'] [Algebra A' Γ(X, U)]
    [MulSemiringAction G Γ(X, U)] [SMulCommClass G A' Γ(X, U)] : Subalgebra A' Γ(X, U) :=
  FixedPoints.subalgebra A' Γ(X, U) G

end GAction

end Work.SymQuot
