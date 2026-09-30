/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary results for the chart factorisation (area SY)

This file collects the auxiliary results used to prove `Work.SymQuot.Chart.exists_chart_factor`:

* `existsUnique_affine_target`: the affine target case at the level of spectra -- an invariant
  morphism `Spec R ⟶ Spec B` factors uniquely through `Spec R^G ⟶ Spec R`;
* the naturality lemmas relating the action on sections to the action on spectra;
* `exists_factor_affine_target`: the affine target case for an affine invariant open subscheme
  `W ⊆ X` and an affine open `V ⊆ Z`;
* `exists_chart_factor_piece`: the "piece" form: if `W ⊆ f ⁻¹ᵁ V` with `W` affine and invariant,
  then the restriction of `f` to `W` factors through the chart map of `W`.
-/
import Mathlib
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.Invariants.fixedPoints_lift
import Submission.Work.SymQuot.Invariants.fixedPoints_isLocalization_away

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Chart

section AffineTarget

variable {G : Type*} [Group G] {R : Type u} [CommRing R] [MulSemiringAction G R]
variable {B : Type u} [CommRing B]

theorem existsUnique_affine_target
    (h : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of B))
    (hh : ∀ g : G, Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g)) ≫ h = h) :
    ∃! g : Spec (CommRingCat.of (FixedPoints.subring R G)) ⟶ Spec (CommRingCat.of B),
      Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring R G))) ≫ g = h := by
  set φ : CommRingCat.of B ⟶ CommRingCat.of R := Spec.preimage h with hφ
  have hφinv : ∀ g : G, φ ≫ CommRingCat.ofHom (MulSemiringAction.toRingHom G R g) = φ := by
    intro g
    have h' := congrArg Spec.preimage (hh g)
    rw [Spec.preimage_comp, Spec.preimage_map] at h'
    exact h'
  have hfix : ∀ (g : G) (b : B), g • (φ.hom b) = φ.hom b := by
    intro g b
    have h' : (φ ≫ CommRingCat.ofHom (MulSemiringAction.toRingHom G R g)).hom = φ.hom :=
      congrArg CommRingCat.Hom.hom (hφinv g)
    have h2 : (φ ≫ CommRingCat.ofHom (MulSemiringAction.toRingHom G R g)).hom b
        = MulSemiringAction.toRingHom G R g (φ.hom b) := rfl
    have hb := RingHom.congr_fun h' b
    rw [h2, MulSemiringAction.toRingHom_apply] at hb
    exact hb
  obtain ⟨ψ, hψ, -⟩ := Work.SymQuot.Invariants.fixedPoints_lift (G := G) φ.hom hfix
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring R G)))
        ≫ Spec.map (CommRingCat.ofHom ψ) = h
    have h2 : (Subring.subtype (FixedPoints.subring R G)).comp ψ = φ.hom := by
      ext b
      exact hψ b
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp ψ (Subring.subtype (FixedPoints.subring R G)),
      h2]
    exact Spec.map_preimage h
  · intro g' hg'
    have hcomp : Spec.preimage g' ≫ CommRingCat.ofHom (Subring.subtype (FixedPoints.subring R G))
        = φ := by
      have h1 := congrArg Spec.preimage hg'
      rw [Spec.preimage_comp, Spec.preimage_map] at h1
      rw [hφ]
      exact h1
    have hge : Spec.preimage g' = CommRingCat.ofHom ψ := by
      ext b
      have hb := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hcomp) b
      simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at hb
      exact hb.trans (hψ b).symm
    calc g' = Spec.map (Spec.preimage g') := (Spec.map_preimage g').symm
      _ = Spec.map (CommRingCat.ofHom ψ) := by rw [hge]

end AffineTarget

section AffineTargetOpen

variable {G : Type u} [Group G] {X : AlgebraicGeometry.Scheme.{u}}

/-- The `CommRingCat` map `A.sectionHom A U hU g` is the sections map of the restricted action. -/
lemma ofHom_sectionHom (A : Work.SymQuot.GAction G X) {U : X.Opens} (hU : A.IsInvariantOpen U)
    (g : G) :
    CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom A U hU g)
      = Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm) := by
  rw [← CommRingCat.ofHom_hom (Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm))]
  rfl

/-- Naturality of `toSpecΓ` with respect to the action on an invariant open. -/
lemma toSpecΓ_sectionHom (A : Work.SymQuot.GAction G X) {U : X.Opens} (hU : A.IsInvariantOpen U)
    (g : G) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom A U hU g)) =
      (A.hom g).resLE U U (le_of_eq (hU g).symm) ≫ U.toSpecΓ := by
  rw [ofHom_sectionHom]
  exact Scheme.Opens.toSpecΓ_SpecMap_appLE (A.hom g) U U (le_of_eq (hU g).symm)

/-- Naturality: `Spec.map` of the action is conjugation by `isoSpec`. -/
lemma spec_map_sectionHom {G : Type u} [Group G] {X : AlgebraicGeometry.Scheme.{u}}
    (A : Work.SymQuot.GAction G X) {W : X.Opens} (hWa : IsAffineOpen W)
    (hWi : A.IsInvariantOpen W) (g : G) :
    Spec.map (CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom A W hWi g⁻¹))
      = hWa.isoSpec.inv ≫ (A.hom g⁻¹).resLE W W (le_of_eq (hWi g⁻¹).symm) ≫ hWa.isoSpec.hom := by
  have hnat : W.toSpecΓ
      ≫ Spec.map (CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom A W hWi g⁻¹))
      = (A.hom g⁻¹).resLE W W (le_of_eq (hWi g⁻¹).symm) ≫ W.toSpecΓ := by
    rw [ofHom_sectionHom]
    exact Scheme.Opens.toSpecΓ_SpecMap_appLE (A.hom g⁻¹) W W (le_of_eq (hWi g⁻¹).symm)
  have hunit : hWa.isoSpec.inv ≫ W.toSpecΓ = 𝟙 (Spec Γ(X, W)) :=
    IsAffineOpen.isoSpec_inv_toSpecΓ hWa
  have hhom : W.toSpecΓ = hWa.isoSpec.hom := (IsAffineOpen.isoSpec_hom hWa).symm
  calc Spec.map (CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom A W hWi g⁻¹))
      = (hWa.isoSpec.inv ≫ W.toSpecΓ)
        ≫ Spec.map (CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom A W hWi g⁻¹)) := by
          rw [hunit, Category.id_comp]
    _ = hWa.isoSpec.inv
        ≫ (W.toSpecΓ
          ≫ Spec.map (CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom A W hWi g⁻¹))) := by
          rw [Category.assoc]
    _ = hWa.isoSpec.inv
        ≫ ((A.hom g⁻¹).resLE W W (le_of_eq (hWi g⁻¹).symm) ≫ W.toSpecΓ) := by rw [hnat]
    _ = (hWa.isoSpec.inv ≫ (A.hom g⁻¹).resLE W W (le_of_eq (hWi g⁻¹).symm)) ≫ W.toSpecΓ := by
          rw [← Category.assoc]
    _ = (hWa.isoSpec.inv ≫ (A.hom g⁻¹).resLE W W (le_of_eq (hWi g⁻¹).symm)) ≫ hWa.isoSpec.hom := by
          rw [hhom]
    _ = hWa.isoSpec.inv ≫ (A.hom g⁻¹).resLE W W (le_of_eq (hWi g⁻¹).symm) ≫ hWa.isoSpec.hom := by
          rw [Category.assoc]

/-- The action ring map on sections is `sectionHom` at the inverse. -/
lemma toRingHom_eq_sectionHom {G : Type u} [Group G] {X : AlgebraicGeometry.Scheme.{u}}
    (A : Work.SymQuot.GAction G X) {W : X.Opens} (hWi : A.IsInvariantOpen W) (g : G) :
    letI : MulSemiringAction G Γ(X, W) := A.sectionMulSemiringAction W hWi
    MulSemiringAction.toRingHom G Γ(X, W) g = Work.SymQuot.GAction.sectionHom A W hWi g⁻¹ := rfl

/-- **The affine target case.**  An invariant morphism from an affine invariant open subscheme
`W ⊆ X` to an affine open subscheme `V ⊆ Z` factors uniquely through the chart of `W`. -/
theorem exists_factor_affine_target (A : Work.SymQuot.GAction G X)
    {W : X.Opens} (hWa : IsAffineOpen W) (hWi : A.IsInvariantOpen W)
    {Y : AlgebraicGeometry.Scheme.{u}} {V : Y.Opens} (hVa : IsAffineOpen V)
    (γ : W.toScheme ⟶ V)
    (hγ : ∀ g : G, (A.hom g).resLE W W (le_of_eq (hWi g).symm) ≫ γ = γ) :
    ∃! g : A.chart W hWi ⟶ V, A.chartMap W hWi ≫ g = γ := by
  letI : MulSemiringAction G Γ(X, W) := A.sectionMulSemiringAction W hWi
  have he_hom : hWa.isoSpec.hom = W.toSpecΓ := IsAffineOpen.isoSpec_hom hWa
  have hchart : A.chartMap W hWi
      = hWa.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X, W) G))) := by
    rw [Work.SymQuot.GAction.chartMap, he_hom]
  have hγ'inv : ∀ g : G,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, W) g))
        ≫ (hWa.isoSpec.inv ≫ γ ≫ hVa.isoSpec.hom)
        = hWa.isoSpec.inv ≫ γ ≫ hVa.isoSpec.hom := by
    intro g
    have hkey : Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, W) g))
        ≫ hWa.isoSpec.inv
        = hWa.isoSpec.inv ≫ (A.hom g⁻¹).resLE W W (le_of_eq (hWi g⁻¹).symm) := by
      rw [toRingHom_eq_sectionHom A hWi g, spec_map_sectionHom A hWa hWi g]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hkey]
    rw [show (hWa.isoSpec.inv ≫ (A.hom g⁻¹).resLE W W (le_of_eq (hWi g⁻¹).symm)) ≫ γ ≫ hVa.isoSpec.hom
        = hWa.isoSpec.inv ≫ ((A.hom g⁻¹).resLE W W (le_of_eq (hWi g⁻¹).symm) ≫ γ) ≫ hVa.isoSpec.hom
        from by simp only [Category.assoc]]
    rw [hγ g⁻¹]
  obtain ⟨g', hg', huniq⟩ := existsUnique_affine_target (hWa.isoSpec.inv ≫ γ ≫ hVa.isoSpec.hom) hγ'inv
  refine ⟨g' ≫ hVa.isoSpec.inv, ?_, ?_⟩
  · change (hWa.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X, W) G)))) ≫ (g' ≫ hVa.isoSpec.inv) = γ
    rw [show (hWa.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X, W) G)))) ≫ (g' ≫ hVa.isoSpec.inv)
        = hWa.isoSpec.hom ≫ (Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X, W) G))) ≫ g') ≫ hVa.isoSpec.inv
        from by simp only [Category.assoc]]
    rw [hg']
    rw [show hWa.isoSpec.hom ≫ (hWa.isoSpec.inv ≫ γ ≫ hVa.isoSpec.hom) ≫ hVa.isoSpec.inv
        = (hWa.isoSpec.hom ≫ hWa.isoSpec.inv) ≫ γ ≫ (hVa.isoSpec.hom ≫ hVa.isoSpec.inv)
        from by simp only [Category.assoc]]
    rw [Iso.hom_inv_id, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  · intro g hg
    change A.chartMap W hWi ≫ g = γ at hg
    have h2 : hWa.isoSpec.inv ≫ (A.chartMap W hWi ≫ g) = hWa.isoSpec.inv ≫ γ := by rw [hg]
    rw [hchart] at h2
    rw [show hWa.isoSpec.inv ≫ ((hWa.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X, W) G)))) ≫ g)
        = (hWa.isoSpec.inv ≫ hWa.isoSpec.hom) ≫ Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X, W) G))) ≫ g
        from by simp only [Category.assoc]] at h2
    rw [Iso.inv_hom_id, Category.id_comp] at h2
    have hstep : Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X, W) G)))
        ≫ (g ≫ hVa.isoSpec.hom) = hWa.isoSpec.inv ≫ γ ≫ hVa.isoSpec.hom := by
      rw [show Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X, W) G))) ≫ (g ≫ hVa.isoSpec.hom)
          = (Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X, W) G))) ≫ g) ≫ hVa.isoSpec.hom
          from by simp only [Category.assoc]]
      rw [h2, Category.assoc]
    have h5 := huniq (g ≫ hVa.isoSpec.hom) hstep
    rw [← h5]
    rw [show (g ≫ hVa.isoSpec.hom) ≫ hVa.isoSpec.inv = g ≫ (hVa.isoSpec.hom ≫ hVa.isoSpec.inv)
        from by simp only [Category.assoc]]
    rw [Iso.hom_inv_id, Category.comp_id]


end AffineTargetOpen

section Piece

variable {G : Type u} [Group G] {X : AlgebraicGeometry.Scheme.{u}}

/-- **The piece map.**  If `W ⊆ X` is an affine `Γ`-invariant open subscheme whose image under an
invariant morphism `f : X ⟶ Y` lies in the affine open `V ⊆ Y`, then the restriction of `f` to `W`
factors through the chart map `W ⟶ chart W`: there is `g : chart W ⟶ V` with
`chartMap W ≫ g ≫ V.ι = W.ι ≫ f`. -/
theorem exists_chart_factor_piece (A : Work.SymQuot.GAction G X)
    {W : X.Opens} (hWa : IsAffineOpen W) (hWi : A.IsInvariantOpen W)
    {Y : AlgebraicGeometry.Scheme.{u}} {V : Y.Opens} (hVa : IsAffineOpen V)
    (f : X ⟶ Y) (hf : A.IsInvariantMorphism f) (hWV : W ≤ f ⁻¹ᵁ V) :
    ∃ g : A.chart W hWi ⟶ V, A.chartMap W hWi ≫ g ≫ V.ι = W.ι ≫ f := by
  have hrange : Set.range ⇑(W.ι ≫ f) ⊆ Set.range ⇑V.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨f (W.ι x), ?_⟩, rfl⟩
    have h1 : W.ι x ∈ f ⁻¹ᵁ V := hWV x.2
    simpa [Set.mem_preimage] using h1
  set fV := IsOpenImmersion.lift V.ι (W.ι ≫ f) hrange with hfV
  have hfV_fac : fV ≫ V.ι = W.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hfV_inv : ∀ g : G, (A.hom g).resLE W W (le_of_eq (hWi g).symm) ≫ fV = fV := by
    intro g
    refine (cancel_mono V.ι).mp ?_
    have hres : (A.hom g).resLE W W (le_of_eq (hWi g).symm) ≫ W.ι = W.ι ≫ A.hom g :=
      Scheme.Hom.resLE_comp_ι (A.hom g) (le_of_eq (hWi g).symm)
    rw [Category.assoc, hfV_fac, ← Category.assoc, hres, Category.assoc, hf g]
  obtain ⟨g, hg, -⟩ := exists_factor_affine_target A hWa hWi hVa fV hfV_inv
  refine ⟨g, ?_⟩
  rw [← Category.assoc, hg, hfV_fac]

end Piece

end Work.SymQuot.Chart
