/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The universal property of `Spec (C ^ Γ)` for a finite group `Γ`

For a finite group `Γ` acting on a commutative ring `C`, a `Γ`-invariant morphism
`f : Spec C ⟶ Z` factors uniquely through `Spec (C^Γ) ⟶ Spec C`, the morphism induced by the
inclusion of the fixed subring.  In other words `Spec (C^Γ)` is the quotient of `Spec C` by the
action of `Γ` in the category of schemes.

The proof is the special case `U = ⊤` of the local factorisation
`Work.SymQuot.Chart.exists_chart_factor`: for the affine scheme `Spec C` and its invariant open
subscheme `⊤`, the chart is `Spec Γ(Spec C, ⊤)^Γ`, and the identification of
`Γ(Spec C, ⊤)^Γ` with `C^Γ` is the `Γ`-equivariance of `Scheme.ΓSpecIso`
(`gammaSpecIso_hom_smul`), packaged in `specFixedPointsEquiv`.
-/
import Mathlib
import Submission.Work.SymQuot.RelQuot.Defs
import Submission.Work.SymQuot.Chart.exists_chart_factor
import Submission.Work.SymQuot.Invariants.fixedPoints_isLocalization_away

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1000000

open scoped AlgebraicGeometry

namespace Work.SymQuot.RelQuot

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

variable {Γ : Type u} [Group Γ] [Fintype Γ] (C : Type u) [CommRing C] [MulSemiringAction Γ C]

/-- The action of `Γ` on the global sections `Γ(Spec C, ⊤)`, induced by the action on `C`
through the action `Work.SymQuot.RelQuot.gActionOfRingAction` on `Spec C`. -/
local instance instMulSemiringActionSections :
    MulSemiringAction Γ Γ(Spec (CommRingCat.of C), ⊤) :=
  (gActionOfRingAction C).sectionMulSemiringAction ⊤ GAction.IsInvariantOpen.top

/-- **`ΓSpecIso` is equivariant.**  Under the canonical ring isomorphism
`Γ(Spec C, ⊤) ≅ C`, the action of `Γ` on the global sections of `Spec C` corresponds to the
action of `Γ` on `C`. -/
lemma gammaSpecIso_hom_smul (g : Γ) (s : Γ(Spec (CommRingCat.of C), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of C)).hom (g • s) =
      g • (Scheme.ΓSpecIso (CommRingCat.of C)).hom s := by
  have hAhom : (gActionOfRingAction C).hom g⁻¹ =
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C g)) := by
    simp only [gActionOfRingAction, inv_inv]
  have h1 : (gActionOfRingAction C).sectionHom ⊤ (GAction.IsInvariantOpen.top) g⁻¹ =
      ((gActionOfRingAction C).hom g⁻¹).appTop.hom := by
    ext t
    rw [GAction.sectionHom_apply]
    have h : Scheme.Hom.appLE ((gActionOfRingAction C).hom g⁻¹) ⊤ ⊤
        (le_of_eq ((GAction.IsInvariantOpen.top (A := gActionOfRingAction C)) g⁻¹).symm) =
        ((gActionOfRingAction C).hom g⁻¹).appTop := by
      rw [appLE_congr_le ((gActionOfRingAction C).hom g⁻¹) _
        (le_rfl : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤
          ((gActionOfRingAction C).hom g⁻¹) ⁻¹ᵁ ⊤)]
      exact Scheme.Hom.appLE_eq_app ((gActionOfRingAction C).hom g⁻¹)
    exact congrArg (fun (φ : Γ(Spec (CommRingCat.of C), ⊤) ⟶
      Γ(Spec (CommRingCat.of C), ⊤)) => φ.hom t) h
  rw [show (g • s) = (gActionOfRingAction C).sectionHom ⊤
      (GAction.IsInvariantOpen.top) g⁻¹ s from rfl, h1, hAhom]
  have h2 := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C g))
  exact congr($(h2) s)

/-- The inverse form of `gammaSpecIso_hom_smul`. -/
lemma gammaSpecIso_inv_smul (g : Γ) (c : C) :
    (Scheme.ΓSpecIso (CommRingCat.of C)).inv (g • c) =
      g • (Scheme.ΓSpecIso (CommRingCat.of C)).inv c := by
  have h := gammaSpecIso_hom_smul C g ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c)
  rw [Iso.inv_hom_id_apply] at h
  calc (Scheme.ΓSpecIso (CommRingCat.of C)).inv (g • c)
      = (Scheme.ΓSpecIso (CommRingCat.of C)).inv
          ((Scheme.ΓSpecIso (CommRingCat.of C)).hom
            (g • (Scheme.ΓSpecIso (CommRingCat.of C)).inv c)) := by rw [h]
    _ = g • (Scheme.ΓSpecIso (CommRingCat.of C)).inv c :=
        Iso.hom_inv_id_apply _ _

/-- **The fixed subrings of `C` and of `Γ(Spec C, ⊤)` are canonically isomorphic**, through the
`Γ`-equivariant isomorphism `Scheme.ΓSpecIso`. -/
noncomputable def specFixedPointsEquiv :
    FixedPoints.subring Γ(Spec (CommRingCat.of C), ⊤) Γ ≃+* FixedPoints.subring C Γ where
  toFun x := ⟨(Scheme.ΓSpecIso (CommRingCat.of C)).hom x.1, fun g => by
    rw [← gammaSpecIso_hom_smul C g x.1, x.2 g]⟩
  invFun c := ⟨(Scheme.ΓSpecIso (CommRingCat.of C)).inv c.1, fun g => by
    rw [← gammaSpecIso_inv_smul C g c.1, c.2 g]⟩
  left_inv x := Subtype.ext (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of C)) x.1)
  right_inv c := Subtype.ext (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of C)) c.1)
  map_mul' x y := Subtype.ext (map_mul _ x.1 y.1)
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)

/-- The subtype maps of the fixed subrings are intertwined by `specFixedPointsEquiv` and
`ΓSpecIso`. -/
lemma subtype_comp_specFixedPointsEquiv :
    (Subring.subtype (FixedPoints.subring C Γ)).comp (specFixedPointsEquiv C).toRingHom =
      ((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom).comp
        (Subring.subtype (FixedPoints.subring Γ(Spec (CommRingCat.of C), ⊤) Γ)) := by
  ext x
  rfl

/-- Translation of `subtype_comp_specFixedPointsEquiv` to the spectra. -/
lemma specMap_subtype_comp_specMap_equiv :
    Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring C Γ))) ≫
        Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).toRingHom) =
      (Spec (CommRingCat.of C)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (Subring.subtype
          (FixedPoints.subring Γ(Spec (CommRingCat.of C), ⊤) Γ))) := by
  have h := congrArg (fun ψ : FixedPoints.subring Γ(Spec (CommRingCat.of C), ⊤) Γ →+* C =>
      Spec.map (CommRingCat.ofHom ψ)) (subtype_comp_specFixedPointsEquiv C)
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
    SpecMap_ΓSpecIso_hom] using h

/-- The chart map of `⊤` for the action on `Spec C`, read through `Scheme.topIso`. -/
lemma topIso_inv_chartMap :
    (Spec (CommRingCat.of C)).topIso.inv ≫
        (gActionOfRingAction C).chartMap ⊤ GAction.IsInvariantOpen.top =
      (Spec (CommRingCat.of C)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (Subring.subtype
          (FixedPoints.subring Γ(Spec (CommRingCat.of C), ⊤) Γ))) := by
  rw [GAction.chartMap, Scheme.Opens.toSpecΓ_top, ← Scheme.topIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- `Spec.map` of the two sides of `specFixedPointsEquiv` are inverse to each other. -/
lemma specMap_equiv_comp_symm :
    Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).symm.toRingHom) =
      𝟙 (Spec (CommRingCat.of (FixedPoints.subring C Γ))) := by
  have hcomp : (specFixedPointsEquiv C).toRingHom.comp
      (specFixedPointsEquiv C).symm.toRingHom = RingHom.id (FixedPoints.subring C Γ) := by
    ext x
    simpa using RingEquiv.apply_symm_apply (specFixedPointsEquiv C) x
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp,
    show CommRingCat.ofHom (RingHom.id (FixedPoints.subring C Γ)) =
      𝟙 (CommRingCat.of (FixedPoints.subring C Γ)) from rfl, Spec.map_id]

/-- `Spec.map` of the two sides of `specFixedPointsEquiv` are inverse to each other. -/
lemma specMap_symm_comp_equiv :
    Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).toRingHom) =
      𝟙 (Spec (CommRingCat.of (FixedPoints.subring
        Γ(Spec (CommRingCat.of C), ⊤) Γ))) := by
  have hcomp : (specFixedPointsEquiv C).symm.toRingHom.comp
      (specFixedPointsEquiv C).toRingHom =
        RingHom.id (FixedPoints.subring Γ(Spec (CommRingCat.of C), ⊤) Γ) := by
    ext x
    simpa using RingEquiv.symm_apply_apply (specFixedPointsEquiv C) x
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp,
    show CommRingCat.ofHom (RingHom.id (FixedPoints.subring Γ(Spec (CommRingCat.of C), ⊤) Γ)) =
      𝟙 (CommRingCat.of (FixedPoints.subring Γ(Spec (CommRingCat.of C), ⊤) Γ)) from rfl,
    Spec.map_id]

/-- The chart map of `⊤` composed with the inverse of `specFixedPointsEquiv` is the quotient map
`Spec C ⟶ Spec (C^Γ)`. -/
lemma chartMap_comp_specMap_symm :
    (gActionOfRingAction C).chartMap ⊤ GAction.IsInvariantOpen.top ≫
        Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).symm.toRingHom) =
      (Spec (CommRingCat.of C)).topIso.hom ≫
        Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring C Γ))) := by
  have h := specMap_subtype_comp_specMap_equiv (Γ := Γ) C
  rw [← topIso_inv_chartMap C] at h
  have h2 := congrArg (fun m => m ≫
    Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).symm.toRingHom)) h
  simp only [Category.assoc] at h2
  rw [specMap_equiv_comp_symm C, Category.comp_id] at h2
  rw [h2, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

open CategoryTheory Limits AlgebraicGeometry in
theorem specFixedPoints_lift {Γ : Type u} [Group Γ] [Fintype Γ] (C : Type u) [CommRing C]
    [MulSemiringAction Γ C] {Z : Scheme.{u}}
    (f : Spec (CommRingCat.of C) ⟶ Z)
    (hf : ∀ g : Γ, Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C g)) ≫ f = f) :
    ∃! h : Spec (CommRingCat.of (FixedPoints.subring C Γ)) ⟶ Z,
      Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring C Γ))) ≫ h = f := by
  classical
  have hf' : (gActionOfRingAction C).IsInvariantMorphism f := fun g => hf g⁻¹
  obtain ⟨g, hg, hg_unique⟩ :=
    Chart.exists_chart_factor (gActionOfRingAction C) (isAffineOpen_top _)
      GAction.IsInvariantOpen.top f hf'
  refine ⟨Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).toRingHom) ≫ g, ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring C Γ))) ≫
        (Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).toRingHom) ≫ g) = f
    rw [← Category.assoc, specMap_subtype_comp_specMap_equiv C, ← topIso_inv_chartMap C,
      Category.assoc, hg, ← Scheme.topIso_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · intro h' hh'
    have hg' : (gActionOfRingAction C).chartMap ⊤ GAction.IsInvariantOpen.top ≫
        (Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).symm.toRingHom) ≫ h') =
        (⊤ : (Spec (CommRingCat.of C)).Opens).ι ≫ f := by
      rw [← Category.assoc, chartMap_comp_specMap_symm C, Category.assoc, hh',
        Scheme.topIso_hom]
    have huniq := hg_unique _ hg'
    calc h' = 𝟙 (Spec (CommRingCat.of (FixedPoints.subring C Γ))) ≫ h' :=
          (Category.id_comp _).symm
      _ = (Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).symm.toRingHom)) ≫ h' := by
          rw [specMap_equiv_comp_symm]
      _ = Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).symm.toRingHom) ≫ h') :=
          Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom (specFixedPointsEquiv C).toRingHom) ≫ g := by
          rw [huniq]

end

end Work.SymQuot.RelQuot
