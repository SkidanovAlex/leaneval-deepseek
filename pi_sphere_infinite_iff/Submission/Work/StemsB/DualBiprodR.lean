import Mathlib
import Submission.Work.Cohomology.isIso_biprod_lift_dualMap

/-!
# The dual of a biproduct of `R`-modules

`Submission/Work/Cohomology/isIso_biprod_lift_dualMap.lean` proves, for `ℤ`-modules, that if
`biprod.desc g₁ g₂ : M ⊞ M ⟶ N` is an isomorphism then so is its transpose
`biprod.lift (g₁^∨) (g₂^∨) : N^∨ ⟶ M^∨ ⊞ M^∨`.  This file is the coefficient-general version
(`Work.StemsB.DualBiprodR.isIso_biprod_lift_dualMap`) needed by the `Y × S⁰` decomposition over an
arbitrary coefficient ring.
-/

set_option linter.unusedSectionVars false

open CategoryTheory Limits

namespace Work.StemsB

noncomputable section

variable {R : Type} [CommRing R]

namespace DualBiprodR

/-- The dual map `f^∨ : B^∨ ⟶ A^∨` of a morphism `f : A ⟶ B` of `R`-modules. -/
def dualMapHom {A B : ModuleCat R} (f : A ⟶ B) :
    ModuleCat.of R (Module.Dual R ↥B) ⟶ ModuleCat.of R (Module.Dual R ↥A) :=
  ModuleCat.ofHom f.hom.dualMap

@[simp]
lemma dualMapHom_hom {A B : ModuleCat R} (f : A ⟶ B) :
    (dualMapHom f).hom = f.hom.dualMap := rfl

lemma dualMapHom_id {A : ModuleCat R} :
    dualMapHom (𝟙 A) = 𝟙 (ModuleCat.of R (Module.Dual R ↥A)) := by
  apply ModuleCat.hom_ext
  simp only [dualMapHom, ModuleCat.hom_id, ModuleCat.hom_ofHom, LinearMap.dualMap_id]

/-- Dualisation is contravariant. -/
lemma dualMapHom_comp {A B C : ModuleCat R} (f : A ⟶ B) (g : B ⟶ C) :
    dualMapHom (f ≫ g) = dualMapHom g ≫ dualMapHom f := by
  apply ModuleCat.hom_ext
  simp only [dualMapHom, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  exact (LinearMap.dualMap_comp_dualMap f.hom g.hom).symm

lemma dualMapHom_add {A B : ModuleCat R} (f g : A ⟶ B) :
    dualMapHom (f + g) = dualMapHom f + dualMapHom g := by
  apply ModuleCat.hom_ext
  simp only [dualMapHom, ModuleCat.hom_add, ModuleCat.hom_ofHom]
  ext φ x
  simp

lemma dualMapHom_zero {A B : ModuleCat R} : dualMapHom (0 : A ⟶ B) = 0 := by
  apply ModuleCat.hom_ext
  simp only [dualMapHom, ModuleCat.hom_zero, ModuleCat.hom_ofHom]
  ext φ x
  simp

/-- The dual `M^∨` of an `R`-module `M`. -/
abbrev dualObj (M : ModuleCat R) : ModuleCat R := ModuleCat.of R (Module.Dual R ↥M)

/-- The canonical isomorphism `(M ⊞ M)^∨ ⟶ M^∨ ⊞ M^∨`. -/
def theta (M : ModuleCat R) : dualObj (M ⊞ M) ⟶ dualObj M ⊞ dualObj M :=
  biprod.lift (dualMapHom (biprod.inl : M ⟶ M ⊞ M))
    (dualMapHom (biprod.inr : M ⟶ M ⊞ M))

/-- Its inverse `M^∨ ⊞ M^∨ ⟶ (M ⊞ M)^∨`. -/
def thetaInv (M : ModuleCat R) : dualObj M ⊞ dualObj M ⟶ dualObj (M ⊞ M) :=
  biprod.desc (dualMapHom (biprod.fst : M ⊞ M ⟶ M))
    (dualMapHom (biprod.snd : M ⊞ M ⟶ M))

/-- Naturality of `biprod.lift` in its common source. -/
lemma biprod_lift_comp {X Y Z U : ModuleCat R} [HasBinaryBiproduct X Y]
    (h : U ⟶ Z) (f : Z ⟶ X) (g : Z ⟶ Y) :
    h ≫ biprod.lift f g = biprod.lift (h ≫ f) (h ≫ g) :=
  biprod.ext_to_iff.mpr ⟨by simp, by simp⟩

/-- Naturality of `biprod.desc` in its common target. -/
lemma biprod_desc_comp {X Y Z W : ModuleCat R} [HasBinaryBiproduct X Y]
    (h : Z ⟶ W) (f : X ⟶ Z) (g : Y ⟶ Z) :
    biprod.desc f g ≫ h = biprod.desc (f ≫ h) (g ≫ h) :=
  biprod.ext_from_iff.mpr ⟨by simp, by simp⟩

lemma biprod_desc_id_zero {X Y : ModuleCat R} :
    biprod.desc (𝟙 X) (0 : Y ⟶ X) = (biprod.fst : X ⊞ Y ⟶ X) :=
  biprod.ext_from_iff.mpr ⟨by simp, by simp⟩

lemma biprod_desc_zero_id {X Y : ModuleCat R} :
    biprod.desc (0 : X ⟶ Y) (𝟙 Y) = (biprod.snd : X ⊞ Y ⟶ Y) :=
  biprod.ext_from_iff.mpr ⟨by simp, by simp⟩

lemma theta_comp_thetaInv (M : ModuleCat R) : theta M ≫ thetaInv M = 𝟙 _ := by
  simp only [theta, thetaInv]
  rw [biprod.lift_desc]
  rw [← dualMapHom_comp (biprod.fst : M ⊞ M ⟶ M) (biprod.inl : M ⟶ M ⊞ M),
      ← dualMapHom_comp (biprod.snd : M ⊞ M ⟶ M) (biprod.inr : M ⟶ M ⊞ M)]
  rw [← dualMapHom_add (biprod.fst ≫ biprod.inl) (biprod.snd ≫ biprod.inr)]
  rw [biprod.total, dualMapHom_id]

lemma thetaInv_comp_theta (M : ModuleCat R) : thetaInv M ≫ theta M = 𝟙 _ := by
  apply biprod.ext_to_iff.mpr
  constructor
  · rw [Category.assoc, theta, biprod.lift_fst, thetaInv, biprod_desc_comp]
    rw [← dualMapHom_comp (biprod.inl : M ⟶ M ⊞ M) (biprod.fst : M ⊞ M ⟶ M),
        ← dualMapHom_comp (biprod.inl : M ⟶ M ⊞ M) (biprod.snd : M ⊞ M ⟶ M)]
    rw [biprod.inl_fst, biprod.inl_snd, dualMapHom_id, dualMapHom_zero]
    rw [biprod_desc_id_zero]
    simp
  · rw [Category.assoc, theta, biprod.lift_snd, thetaInv, biprod_desc_comp]
    rw [← dualMapHom_comp (biprod.inr : M ⟶ M ⊞ M) (biprod.fst : M ⊞ M ⟶ M),
        ← dualMapHom_comp (biprod.inr : M ⟶ M ⊞ M) (biprod.snd : M ⊞ M ⟶ M)]
    rw [biprod.inr_fst, biprod.inr_snd, dualMapHom_zero, dualMapHom_id]
    rw [biprod_desc_zero_id]
    simp

end DualBiprodR

open DualBiprodR

/-- If `biprod.desc g₁ g₂ : M ⊞ M ⟶ N` is an isomorphism of `R`-modules, then so is its
transpose `biprod.lift (g₁^∨) (g₂^∨) : N^∨ ⟶ M^∨ ⊞ M^∨`. -/
theorem isIso_biprod_lift_dualMap {M N : ModuleCat R} (g₁ g₂ : M ⟶ N)
    [CategoryTheory.IsIso (CategoryTheory.Limits.biprod.desc g₁ g₂)] :
    CategoryTheory.IsIso (CategoryTheory.Limits.biprod.lift
      (ModuleCat.ofHom g₁.hom.dualMap) (ModuleCat.ofHom g₂.hom.dualMap)) := by
  change IsIso (biprod.lift (dualMapHom g₁) (dualMapHom g₂))
  haveI hTd : IsIso (dualMapHom (biprod.desc g₁ g₂)) := by
    refine IsIso.mk ⟨dualMapHom (CategoryTheory.inv (biprod.desc g₁ g₂)), ?_, ?_⟩
    · rw [← dualMapHom_comp (CategoryTheory.inv (biprod.desc g₁ g₂)) (biprod.desc g₁ g₂),
          IsIso.inv_hom_id, dualMapHom_id]
    · rw [← dualMapHom_comp (biprod.desc g₁ g₂) (CategoryTheory.inv (biprod.desc g₁ g₂)),
          IsIso.hom_inv_id, dualMapHom_id]
  haveI hθ : IsIso (theta M) :=
    IsIso.mk ⟨thetaInv M, theta_comp_thetaInv M, thetaInv_comp_theta M⟩
  have hg1 : dualMapHom g₁ = dualMapHom (biprod.inl ≫ biprod.desc g₁ g₂) := by
    rw [biprod.inl_desc g₁ g₂]
  have h1 : dualMapHom g₁
      = dualMapHom (biprod.desc g₁ g₂) ≫ dualMapHom (biprod.inl : M ⟶ M ⊞ M) := by
    rw [hg1, dualMapHom_comp]
  have hg2 : dualMapHom g₂ = dualMapHom (biprod.inr ≫ biprod.desc g₁ g₂) := by
    rw [biprod.inr_desc g₁ g₂]
  have h2 : dualMapHom g₂
      = dualMapHom (biprod.desc g₁ g₂) ≫ dualMapHom (biprod.inr : M ⟶ M ⊞ M) := by
    rw [hg2, dualMapHom_comp]
  rw [h1, h2]
  have h3 : biprod.lift (dualMapHom (biprod.desc g₁ g₂) ≫ dualMapHom (biprod.inl : M ⟶ M ⊞ M))
      (dualMapHom (biprod.desc g₁ g₂) ≫ dualMapHom (biprod.inr : M ⟶ M ⊞ M))
      = dualMapHom (biprod.desc g₁ g₂) ≫ theta M := by
    rw [theta, biprod_lift_comp]
  rw [h3]
  haveI : IsIso (dualMapHom (biprod.desc g₁ g₂) ≫ theta M) := inferInstance
  exact inferInstance

end

end Work.StemsB
