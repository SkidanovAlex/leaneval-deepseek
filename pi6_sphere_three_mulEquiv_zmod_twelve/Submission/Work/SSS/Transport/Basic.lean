import Mathlib
import Submission.Work.SSS.serreE1Transport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Basic API for the fibre transport of a Serre fibration

Functoriality of `Work.SSS.HZHomeoIso`, the identification of the endpoint `eqToIso` factors of
`Work.SSS.transportIsoPath` with the homology isomorphism induced by the canonical homeomorphism of
fibres, and a general cancellation lemma for isomorphisms in a category.
-/

set_option autoImplicit false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.SSS

noncomputable section

/-! ## Functoriality of `HZHomeoIso` -/

theorem HZHomeoIso_refl {X : Type} [TopologicalSpace X] (j : ℕ) :
    HZHomeoIso (Homeomorph.refl X) j = Iso.refl _ := by
  have h1 : (TopCat.isoOfHomeo (Homeomorph.refl X) : TopCat.of X ≅ TopCat.of X) = Iso.refl _ := by
    refine Iso.ext ?_
    show TopCat.ofHom (↑(Homeomorph.refl X) : C(X, X)) = 𝟙 (TopCat.of X)
    rfl
  simp only [HZHomeoIso, h1, CategoryTheory.Functor.mapIso_refl]
  rfl

theorem HZHomeoIso_trans {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (e₁ : X ≃ₜ Y) (e₂ : Y ≃ₜ Z) (j : ℕ) :
    HZHomeoIso (e₁.trans e₂) j = HZHomeoIso e₁ j ≪≫ HZHomeoIso e₂ j := by
  have h1 : (TopCat.isoOfHomeo (e₁.trans e₂ : TopCat.of X ≃ₜ TopCat.of Z)
        : TopCat.of X ≅ TopCat.of Z) =
      (TopCat.isoOfHomeo (e₁ : TopCat.of X ≃ₜ TopCat.of Y) :
          TopCat.of X ≅ TopCat.of Y) ≪≫
        (TopCat.isoOfHomeo (e₂ : TopCat.of Y ≃ₜ TopCat.of Z) :
          TopCat.of Y ≅ TopCat.of Z) := by
    refine Iso.ext ?_
    show TopCat.ofHom (↑(e₁.trans e₂) : C(X, Z)) =
      TopCat.ofHom (↑e₁ : C(X, Y)) ≫ TopCat.ofHom (↑e₂ : C(Y, Z))
    rfl
  simp only [HZHomeoIso, h1, CategoryTheory.Functor.mapIso_trans]
  try rfl

theorem HZHomeoIso_symm {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (j : ℕ) : (HZHomeoIso e j).symm = HZHomeoIso e.symm j := by
  have h1 : (TopCat.isoOfHomeo (e.symm : TopCat.of Y ≃ₜ TopCat.of X) :
        TopCat.of Y ≅ TopCat.of X) =
      (TopCat.isoOfHomeo (e : TopCat.of X ≃ₜ TopCat.of Y) : TopCat.of X ≅ TopCat.of Y).symm := by
    refine Iso.ext ?_
    show TopCat.ofHom (↑(e.symm) : C(Y, X)) = TopCat.ofHom (↑(e.symm) : C(Y, X))
    rfl
  simp only [HZHomeoIso, h1, CategoryTheory.Functor.mapIso_symm]
  try rfl

/-- The forward map of `HZHomeoIso` is the homology map of the underlying continuous map. -/
theorem HZHomeoIso_hom {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (j : ℕ) :
    (HZHomeoIso e j).hom =
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom (e : C(X, Y)))) j := by
  simp only [HZHomeoIso, TopCat.isoOfHomeo, Work.Cohomology.chainMap, CategoryTheory.Functor.mapIso_hom]
  exact HomologicalComplex.homologyFunctor_map (ModuleCat ℤ) (ComplexShape.down ℕ) j _

/-! ## The canonical homeomorphism between the fibres over equal base points -/

/-- The canonical homeomorphism `p⁻¹b ≃ₜ p⁻¹b'` induced by an equality `b = b'`. -/
def homeoFibreEq {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {b b' : B}
    (h : b = b') : Work.StemsB.fibre p b ≃ₜ Work.StemsB.fibre p b' where
  toFun e := ⟨e.1, e.2.trans h⟩
  invFun e := ⟨e.1, e.2.trans h.symm⟩
  left_inv e := by cases h; rfl
  right_inv e := by cases h; rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

/-- **The endpoint correction of `Work.SSS.transportIsoPath` is the homology isomorphism induced
by the canonical homeomorphism of the fibres.** -/
theorem eqToIso_fibre_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    {b b' : B} (h : b = b') (j : ℕ) :
    CategoryTheory.eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) h) =
      HZHomeoIso (homeoFibreEq p h) j := by
  cases h
  rw [show homeoFibreEq p (rfl : b = b) = Homeomorph.refl _ from
    Homeomorph.ext (fun e => Subtype.ext rfl)]
  rw [HZHomeoIso_refl]
  simp only [CategoryTheory.eqToIso_refl]

/-! ## Cancelling a common morphism on the right -/

/-- `asIso` does not depend on the proof of `IsIso`. -/
theorem asIso_congr {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (h₁ h₂ : IsIso f) :
    @asIso _ _ X Y f h₁ = @asIso _ _ X Y f h₂ := by
  refine Iso.ext ?_
  rfl

/-- Homology maps are unchanged by an equality of morphisms. -/
theorem chain_homologyMap_congr {X Y : TopCat} {f g : X ⟶ Y} (h : f = g) (j : ℕ) :
    HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) j =
      HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y g) j := by
  rw [h]

/-- The homology map of a composite of continuous maps. -/
theorem chain_homologyMap_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (j : ℕ) :
    HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) j ≫
        HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ Y Z g) j =
      HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Z (f ≫ g)) j := by
  rw [← HomologicalComplex.homologyMap_comp]
  congr 1
  simp only [Work.Cohomology.chainMap, CategoryTheory.Functor.map_comp]


/-- **Two transports computed through different ambient objects agree.**  If `i₀, i₁, h₀, h₁, k₀, k₁`
are isomorphisms and the morphisms `i₀ ≫ j` and `h₀ ≫ k₀` (resp. `i₁ ≫ j` and `h₁ ≫ k₁`) agree for
a common morphism `j`, then the transport `i₀ ≫ i₁⁻¹` between the two sources agrees with the one
computed via the factorisation. -/
theorem iso_cancel {C : Type*} [Category C] {A B D C₁ C₂ E : C}
    (i₀ : A ≅ D) (i₁ : B ≅ D) (h₀ : A ≅ C₁) (h₁ : B ≅ C₂) (k₀ : C₁ ≅ E) (k₁ : C₂ ≅ E)
    (j : D ⟶ E) (e₀ : i₀.hom ≫ j = h₀.hom ≫ k₀.hom) (e₁ : i₁.hom ≫ j = h₁.hom ≫ k₁.hom) :
    i₀.hom ≫ i₁.inv = h₀.hom ≫ k₀.hom ≫ k₁.inv ≫ h₁.inv := by
  have hkey : j = i₁.inv ≫ h₁.hom ≫ k₁.hom := by
    rw [← Iso.inv_hom_id_assoc i₁ j, e₁]
  calc i₀.hom ≫ i₁.inv
      = i₀.hom ≫ i₁.inv ≫ h₁.hom ≫ k₁.hom ≫ k₁.inv ≫ h₁.inv := by
        simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (i₀.hom ≫ (i₁.inv ≫ h₁.hom ≫ k₁.hom)) ≫ (k₁.inv ≫ h₁.inv) := by
        simp only [Category.assoc]
    _ = (i₀.hom ≫ j) ≫ (k₁.inv ≫ h₁.inv) := by rw [← hkey]
    _ = (h₀.hom ≫ k₀.hom) ≫ (k₁.inv ≫ h₁.inv) := by rw [e₀]
    _ = h₀.hom ≫ k₀.hom ≫ k₁.inv ≫ h₁.inv := by simp only [Category.assoc]

end

end Work.SSS
