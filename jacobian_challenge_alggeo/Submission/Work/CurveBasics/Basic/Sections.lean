/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `k`-algebra structure on sections of a curve

For a curve `C` over a field `k` and an open `U ⊆ C`, the ring of sections `Γ(C, U)`
carries a natural `k`-algebra structure, induced by the structure morphism `C ⟶ Spec k`
together with `Γ(Spec k) ≅ k`.

This file records that structure and the two facts about it that the surrounding
development uses:

* `Work.CurveBasics.Curve.specMap_algebraMap_sections`: the structure morphism of the
  affine open `Spec Γ(C, U)` is `Spec.map (algebraMap k Γ(C, U)) = fromSpec ≫ C.hom`;
* `Work.CurveBasics.Curve.isScalarTower_sections`: the resulting scalar tower
  `k ⟶ Γ(C, U) ⟶ K(C)`.
-/
import Mathlib
import Submission.Work.CurveBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The sections `Γ(C, U)` of a curve, as a `k`-algebra via the structure morphism. -/
noncomputable instance instAlgebraSections (C : Curve k) (U : C.left.Opens) :
    Algebra k Γ(C.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.appLE ⊤ U le_top).hom.toAlgebra

/-- The affine open `Spec Γ(C, U)` sits over `Spec k` via `Spec.map (algebraMap k Γ(C, U))`,
which is `fromSpec ≫ C.hom`. -/
theorem specMap_algebraMap_sections (C : Curve k) {U : C.left.Opens} (hU : IsAffineOpen U) :
    Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.left, U))) = hU.fromSpec ≫ C.hom := by
  have key : Spec.map (C.hom.appLE ⊤ U (le_top : U ≤ C.hom ⁻¹ᵁ ⊤)) ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv = hU.fromSpec ≫ C.hom := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (f := C.hom)
      (U := (⊤ : (Spec (CommRingCat.of k)).Opens)) (V := U)
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_top : U ≤ C.hom ⁻¹ᵁ ⊤)
    rwa [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← key, ← Spec.map_comp]
  rw [show (CommRingCat.ofHom (algebraMap k Γ(C.left, U))) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        C.hom.appLE ⊤ U (le_top : U ≤ C.hom ⁻¹ᵁ ⊤) from rfl]

/-- The scalar tower `k ⟶ Γ(C, U) ⟶ K(C)`. -/
theorem isScalarTower_sections (C : Curve k) (U : C.left.Opens) [Nonempty U] :
    IsScalarTower k Γ(C.left, U) C.functionField := by
  haveI : Nonempty (⊤ : C.left.Opens) := ⟨⟨genericPoint C.left, trivial⟩⟩
  have hgerm : C.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
      C.left.germToFunctionField U = C.left.germToFunctionField (⊤ : C.left.Opens) :=
    TopCat.Presheaf.germ_res C.left.presheaf (homOfLE (le_top : U ≤ ⊤))
      (genericPoint C.left) _
  have hgerm_apply (y : Γ(C.left, ⊤)) :
      C.left.germToFunctionField (⊤ : C.left.Opens) y =
      C.left.germToFunctionField U (C.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op y) := by
    have h := congrArg (fun (f : Γ(C.left, ⊤) ⟶ C.functionField) => f y) hgerm
    simpa only [ConcreteCategory.comp_apply] using h.symm
  apply IsScalarTower.of_algebraMap_eq
  intro a
  have htop : C.hom.appLE ⊤ U (le_top : U ≤ C.hom ⁻¹ᵁ ⊤) =
      C.hom.appTop ≫ C.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := rfl
  show C.left.germToFunctionField (⊤ : C.left.Opens)
      (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)) =
    C.left.germToFunctionField U
      (C.hom.appLE ⊤ U (le_top : U ≤ C.hom ⁻¹ᵁ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a))
  rw [htop, ConcreteCategory.comp_apply]
  exact hgerm_apply _

end

end Curve

end Work.CurveBasics
