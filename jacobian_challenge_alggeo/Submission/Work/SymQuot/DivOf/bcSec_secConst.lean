/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `bcSec` commutes with the constant sections

For a tower of field extensions `K → F → F''` and an open `V ⊆ C`, the pullback of sections
`bcSec : Γ(C_F, V_F) →+* Γ(C_{F''}, V_{F''})` along the tower morphism `C_{F''} ⟶ C_F`
(`BCSquareBaseChange.towerHom`) sends the constant section of `c ∈ F` to the constant section
of its image `algebraMap F F'' c ∈ F''`.

The key point is that the tower square `C_{F''} ⟶ C_F` over `Spec F'' ⟶ Spec F` is commutative
(`BCSquareBaseChange.towerHom_snd`) and that the constant sections are the pullbacks of the
structure morphisms.  This is proved in the general form `appLE_secOf` below: for a morphism of
schemes `f : X ⟶ Y`, structure morphisms `p : Y ⟶ Spec F`, `q : X ⟶ Spec F''` with
`f ≫ p = q ≫ Spec.map (ofHom φ)` and opens `V ≤ f ⁻¹ᵁ U`, the pullback `f.appLE U V _` sends the
constant section of `c` to the constant section of `φ c`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSimpArgs false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

open Work.CurveBasics

/-! ## The constant section of a scheme over `Spec F` -/

/-- **The constant section** of a scheme `Y` over `Spec F` on an open `U ⊆ Y`: the pullback of
`c ∈ F` along the structure morphism `Y ⟶ Spec F`, followed by the restriction `Γ(Y,⊤) → Γ(Y,U)`.
For `Y = C_F` this is `secConst C F U`. -/
noncomputable def secOf {F : Type u} [Field F] {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of F))
    (U : Y.Opens) : F →+* Γ(Y, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop ≫
    Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom

/-- **Pullback of constant sections.**  Let `f : X ⟶ Y` be a morphism of schemes over a square
`Spec F'' ⟶ Spec F`, i.e. `f ≫ p = q ≫ Spec.map (ofHom φ)` for structure morphisms `p`, `q` and
`φ : F →+* F''`.  Then pulling back the constant section of `c ∈ F` from an open `U ⊆ Y`
(over the open `V ⊇ f ⁻¹ᵁ U` of `X`) gives the constant section of `φ c`. -/
lemma appLE_secOf {X Y : Scheme.{u}} (f : X ⟶ Y) {F F' : Type u} [Field F] [Field F']
    (p : Y ⟶ Spec (CommRingCat.of F)) (q : X ⟶ Spec (CommRingCat.of F'))
    (φ : F →+* F') (h : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom φ))
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (c : F) :
    f.appLE U V e (secOf p U c) = secOf q V (φ c) := by
  set M : Γ(X, ⊤) ⟶ Γ(X, V) := X.presheaf.map (homOfLE (e.trans
      ((TopologicalSpace.Opens.map f.base).map (homOfLE (le_top : U ≤ ⊤))).le)).op with hM
  have htop : Scheme.Hom.appTop p ≫ Scheme.Hom.appTop f
      = Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ)) ≫ Scheme.Hom.appTop q := by
    rw [← Scheme.Hom.comp_appTop f p, h, Scheme.Hom.comp_appTop]
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
        Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ))
      = (CommRingCat.ofHom φ) ≫ (Scheme.ΓSpecIso (CommRingCat.of F')).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  have hres : M = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [hM]
    try congr 1
  have hmapM : Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ Scheme.Hom.appLE f U V e
      = Scheme.Hom.appTop f ≫ M := by
    rw [hM]
    exact Scheme.Hom.map_appLE f (U := U) e (homOfLE (le_top : U ≤ ⊤)).op
  have key : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ Scheme.Hom.appTop p ≫
        Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ Scheme.Hom.appLE f U V e
      = (CommRingCat.ofHom φ) ≫ ((Scheme.ΓSpecIso (CommRingCat.of F')).inv ≫
          Scheme.Hom.appTop q ≫ X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) := by
    rw [hmapM]
    rw [← Category.assoc (f := Scheme.Hom.appTop p) (g := Scheme.Hom.appTop f) (h := M)]
    rw [htop]
    rw [Category.assoc (f := Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ)))
        (g := Scheme.Hom.appTop q) (h := M)]
    rw [← Category.assoc (f := (Scheme.ΓSpecIso (CommRingCat.of F)).inv)
        (g := Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ))) (h := Scheme.Hom.appTop q ≫ M)]
    rw [hnat]
    rw [Category.assoc]
    try rw [hres]
  have helem := congrArg (fun g : CommRingCat.of F ⟶ Γ(X, V) => g.hom c) key
  simp only [CommRingCat.comp_apply, CommRingCat.ofHom_apply] at helem
  rw [show f.appLE U V e (secOf p U c)
      = (Scheme.Hom.appLE f U V e).hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c))) from rfl,
      show secOf q V (φ c) = (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
          (q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F')).inv.hom (φ c))) from rfl]
  exact helem

/-- **`bcSec` commutes with the constant sections.**  Pulling back the constant section `c` of
`F` along the tower morphism `C_{F''} ⟶ C_F` gives the constant section of `algebraMap F F'' c`. -/
theorem bcSec_secConst {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (F F'' : Type u) [Field F] [Field F''] [Algebra K F] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (V : C.left.Opens) (c : F) :
    bcSec (C := C) F F'' V (secConst C F V c) = secConst C F'' V (algebraMap F F'' c) := by
  have h := appLE_secOf (X := (C.baseChange F'').left) (Y := (C.baseChange F).left)
      (f := BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F''))
      (p := (C.baseChange F).hom) (q := (C.baseChange F'').hom)
      (φ := algebraMap F F'')
      (BCSquareBaseChange.towerHom_snd (C := C) (F := F) (F' := F''))
      (C.bcOpens F V) (C.bcOpens F'' V)
      (le_of_eq (towerHom_preimage_bcOpens (C := C) F F'' V).symm) c
  show (Scheme.Hom.appLE (BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F''))
      (C.bcOpens F V) (C.bcOpens F'' V)
      (le_of_eq (towerHom_preimage_bcOpens (C := C) F F'' V).symm))
      (secOf (C.baseChange F).hom (C.bcOpens F V) c)
    = secOf (C.baseChange F'').hom (C.bcOpens F'' V) (algebraMap F F'' c)
  exact h

end Work.SymQuot.DivOf
