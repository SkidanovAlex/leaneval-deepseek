/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Cohomology of a product is invariant under homotopy equivalence of the factors

If `X₁` and `X₂` are homotopy equivalent spaces and `Y₁` and `Y₂` are homotopy equivalent
spaces, then the products `X₁ × Y₁` and `X₂ × Y₂` are homotopy equivalent, hence their
(cohomology groups with rational coefficients) agree in every degree.

The homotopy equivalence of the products is `f₁ ⊗ₘ f₂` with inverse `g₁ ⊗ₘ g₂`, where the
homotopy `f₁ ≫ g₁ ~ 𝟙 X₁` is combined with `f₂ ≫ g₂ ~ 𝟙 Y₁` by `ContinuousMap.Homotopy.prodMap`;
the point is that in `TopCat` the monoidal product is the cartesian product of spaces, so that
the tensor product of morphisms is the product of the underlying maps.  The conclusion then
follows from `Submission.Sphere.H_iso_of_homotopyEquiv`, i.e. homotopy invariance of cohomology.
-/
import Mathlib
import Submission.Work.Sphere.Suspension

namespace Work.Sphere

open CategoryTheory MonoidalCategory

/-- The tensor product of two homotopy self-maps in `TopCat` is the product of the underlying
continuous maps: this is the equality of continuous maps underlying
`(f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂)`. -/
lemma tensorHom_comp_hom {X₁ X₂ Y₁ Y₂ : TopCat.{0}}
    (f₁ : X₁ ⟶ X₂) (g₁ : X₂ ⟶ X₁) (f₂ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₁) :
    ((f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂)).hom
      = (f₁ ≫ g₁).hom.prodMap (f₂ ≫ g₂).hom := by
  ext p; rfl

/-- The identity of a product in `TopCat` is the product of the identities. -/
lemma id_tensor_hom (X Y : TopCat.{0}) :
    (𝟙 (X ⊗ Y) : X ⊗ Y ⟶ X ⊗ Y).hom
      = (ContinuousMap.id X).prodMap (ContinuousMap.id Y) := rfl

/-- The product of two homotopy self-maps of `TopCat`: if `h₁ : f₁ ≫ g₁ ~ 𝟙 X₁` and
`h₂ : f₂ ≫ g₂ ~ 𝟙 Y₁` then `f₁ ⊗ f₂` and `g₁ ⊗ g₂` are inverse up to homotopy. -/
noncomputable def homotopy_tensorHom {X₁ X₂ Y₁ Y₂ : TopCat.{0}}
    (f₁ : X₁ ⟶ X₂) (g₁ : X₂ ⟶ X₁)
    (hfg₁ : TopCat.Homotopy (f₁ ≫ g₁) (𝟙 X₁))
    (f₂ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₁)
    (hfg₂ : TopCat.Homotopy (f₂ ≫ g₂) (𝟙 Y₁)) :
    TopCat.Homotopy ((f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂)) (𝟙 (X₁ ⊗ Y₁)) :=
  (ContinuousMap.Homotopy.prodMap hfg₁ hfg₂).cast
    (tensorHom_comp_hom f₁ g₁ f₂ g₂).symm (id_tensor_hom X₁ Y₁).symm

theorem H_iso_prod {X₁ X₂ Y₁ Y₂ : TopCat.{0}}
    (f₁ : X₁ ⟶ X₂) (g₁ : X₂ ⟶ X₁)
    (hfg₁ : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp f₁ g₁) (CategoryTheory.CategoryStruct.id X₁))
    (hgf₁ : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp g₁ f₁) (CategoryTheory.CategoryStruct.id X₂))
    (f₂ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₁)
    (hfg₂ : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp f₂ g₂) (CategoryTheory.CategoryStruct.id Y₁))
    (hgf₂ : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp g₂ f₂) (CategoryTheory.CategoryStruct.id Y₂))
    (m : ℕ) :
    Nonempty (Submission.Cohomology.H
        (TopCat.toSSet.obj (CategoryTheory.MonoidalCategoryStruct.tensorObj X₁ Y₁)) ℚ m
      ≃ₗ[ℚ] Submission.Cohomology.H
        (TopCat.toSSet.obj (CategoryTheory.MonoidalCategoryStruct.tensorObj X₂ Y₂)) ℚ m) :=
  Submission.Sphere.H_iso_of_homotopyEquiv (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (f₁ ⊗ₘ f₂) (g₁ ⊗ₘ g₂)
    (homotopy_tensorHom f₁ g₁ hfg₁ f₂ g₂ hfg₂)
    (homotopy_tensorHom g₁ f₁ hgf₁ g₂ f₂ hgf₂) m

end Work.Sphere
