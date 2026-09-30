import Mathlib
import Submission.Work.SSSR.faceD_iota
import Submission.Work.Pi6.MSS.sigmaConstTensorIsoIso_iota_single
import Submission.Work.Pi6.MSS.normalizedCoeffIsoIso_hom_f
import Submission.Work.Pi6.MSS.iotaNormalizedChainComplex_eq_sigma_iota
import Submission.Work.Pi6.MSS.normalizedChainComplexCoprodIso_iota
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The explicit coefficient isomorphism of the E¹ page on a single generator

This file computes, on the canonical generator, the explicit coefficient isomorphism
`Work.SSSR.serreE1CoefIsoIso X M d : (∐_{σ ∈ nIndex X d} M) ≅ (N_*(X) ⊗ M)_d` of the E¹ page.
The isomorphism is by construction the composite

`(coprodReindexIso).symm ≪≫ normalizedChainComplexCoprodIso ≪≫ normalizedCoeffIsoIso ≪≫
  (tensorComplexIsoExpTensIso).symm`,

and each of the four factors is evaluated on the relevant coproduct inclusion in the four auxiliary
files `sigmaConstTensorIsoIso_iota_single`, `normalizedCoeffIsoIso_hom_f`,
`iotaNormalizedChainComplex_eq_sigma_iota` and `normalizedChainComplexCoprodIso_iota`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Pi6.MSS

/-- The explicit coefficient isomorphism `serreE1CoefIsoIso : (∐_{σ ∈ nIndex X d} M) ≅ (N_*(X) ⊗ M)_d`
of the E¹ page sends the canonical generator `ι_σ(m)` to `splitX (e_σ ⊗ m)`, where `e_σ` is the
normalized chain of the nondegenerate simplex underlying `σ` and `splitX` is the inclusion of the
`(d,0)`-summand of the tensor complex `N_*(X) ⊗ M`. -/
theorem serreE1CoefIsoIso_iota_single (𝕜 : Type) [Field 𝕜] (X : SSet.{0}) (M : ModuleCat 𝕜) (d : ℕ)
    (σ : Work.SSSR.nIndex X d) (m : ↥M) :
    (Work.SSSR.serreE1CoefIsoIso X M d).hom.hom
        ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex X d => M) σ).hom m)
      = Work.SSSR.splitX (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)) M d
          (TensorProduct.tmul 𝕜
            ((X.ιNormalizedChainComplex (R := ModuleCat.of 𝕜 𝕜)
              (Work.SSSR.nIndexBase X σ)).hom 1) m) := by
  -- Step 1: `serreE1CoefIsoIso` is the composite of its four defining factors.
  have hcomp : (Work.SSSR.serreE1CoefIsoIso X M d).hom
      = (Work.SSSR.coprodReindexIso X d M).inv ≫
        (Work.SSSR.normalizedChainComplexCoprodIso X M d).hom ≫
        (Work.SSSR.normalizedCoeffIsoIso X M).hom.f d ≫
        Work.SSSR.splitX (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)) M d := by
    haveI hc : ∀ n, IsIso ((Work.SSSR.split (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)) M).f n) :=
      fun n => ⟨Work.SSSR.collapseX _ M n, Work.SSSR.splitX_collapseX _ M n,
        Work.SSSR.collapseX_splitX _ M n⟩
    haveI hs : IsIso (Work.SSSR.split (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)) M) :=
      HomologicalComplex.Hom.isIso_of_components _
    haveI hd : IsIso (Work.SSSR.splitX (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)) M d) := hc d
    have hg : (Work.SSSR.tensorComplexIsoExpTensIso
          (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)) M).hom.f d
        = CategoryTheory.inv (Work.SSSR.splitX (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)) M d) := by
      unfold Work.SSSR.tensorComplexIsoExpTensIso
      rw [CategoryTheory.Iso.symm_hom, CategoryTheory.asIso_inv,
        HomologicalComplex.Hom.inv_f_apply]
      rfl
    have hlast : (CategoryTheory.asIso ((Work.SSSR.tensorComplexIsoExpTensIso
          (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)) M).hom.f d)).inv
        = Work.SSSR.splitX (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)) M d := by
      rw [CategoryTheory.asIso_inv]
      simp only [hg]
      exact CategoryTheory.IsIso.inv_inv
    unfold Work.SSSR.serreE1CoefIsoIso
    simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.asIso_hom, hlast]
  -- Step 2: the inverse form of the generator formula for `sigmaConstTensorIsoIso`.
  have hι : ∀ (S : Type) (t : S), CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.Sigma.ι (fun _ : S => M) t)
        (CategoryTheory.inv ((Work.SSSR.sigmaConstTensorIsoIso M).hom.app S))
      = CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonoidalCategory.leftUnitor M).inv
        (MonoidalCategoryStruct.whiskerRight
          (CategoryTheory.Limits.Sigma.ι (fun _ : S => ModuleCat.of 𝕜 𝕜) t) M) := by
    intro S t
    have h := sigmaConstTensorIsoIso_iota_single (R := 𝕜) M S t
    have h2 : CategoryTheory.Limits.Sigma.ι (fun _ : S => M) t
        = ((CategoryTheory.MonoidalCategory.leftUnitor M).inv ≫
            MonoidalCategoryStruct.whiskerRight
              (CategoryTheory.Limits.Sigma.ι (fun _ : S => ModuleCat.of 𝕜 𝕜) t) M)
          ≫ (Work.SSSR.sigmaConstTensorIsoIso M).hom.app S := by
      rw [Category.assoc, h, ← Category.assoc, CategoryTheory.Iso.inv_hom_id, Category.id_comp]
    rw [h2, Category.assoc, Category.assoc, CategoryTheory.IsIso.hom_inv_id, Category.comp_id]
  -- Step 3: the four factors, evaluated on the generator.
  have h1 : CategoryTheory.CategoryStruct.comp
        (Sigma.ι (fun _ : Work.SSSR.nIndex X d => M) σ)
        (Work.SSSR.coprodReindexIso X d M).inv
      = Sigma.ι (fun _ : X.nonDegenerate d => M)
          (⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩ : X.nonDegenerate d) := by
    rw [Work.SSSR.coprodReindexIso_inv_ι, Work.SSSR.nIndexEquiv_symm_apply]
  have h2 : CategoryTheory.CategoryStruct.comp
        (Sigma.ι (fun _ : X.nonDegenerate d => M)
          (⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩ : X.nonDegenerate d))
        (Work.SSSR.normalizedChainComplexCoprodIso X M d).hom
      = X.ιNormalizedChainComplex (R := M) (Work.SSSR.nIndexBase X σ) :=
    normalizedChainComplexCoprodIso_iota X M d ⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩
  have h3 : X.ιNormalizedChainComplex (R := M) (Work.SSSR.nIndexBase X σ)
      = Sigma.ι (fun _ : X.nonDegenerate d => M)
          (⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩ : X.nonDegenerate d) :=
    iotaNormalizedChainComplex_eq_sigma_iota X (Work.SSSR.nIndexBase X σ) (Work.SSSR.nIndexBase_mem X σ)
  have h4 : X.ιNormalizedChainComplex (R := ModuleCat.of 𝕜 𝕜) (Work.SSSR.nIndexBase X σ)
      = Sigma.ι (fun _ : X.nonDegenerate d => ModuleCat.of 𝕜 𝕜)
          (⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩ : X.nonDegenerate d) :=
    iotaNormalizedChainComplex_eq_sigma_iota X (Work.SSSR.nIndexBase X σ) (Work.SSSR.nIndexBase_mem X σ)
  have hcf : (Work.SSSR.normalizedCoeffIsoIso X M).hom.f d
      = CategoryTheory.inv ((Work.SSSR.sigmaConstTensorIsoIso M).hom.app (X.nonDegenerate d)) :=
    normalizedCoeffIsoIso_hom_f X M d
  have e1 : (ModuleCat.Hom.hom (Work.SSSR.coprodReindexIso X d M).inv)
        ((ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSSR.nIndex X d => M) σ)) m)
      = (ModuleCat.Hom.hom (Sigma.ι (fun _ : X.nonDegenerate d => M)
          ⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩)) m := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, h1]
  have e2 : (ModuleCat.Hom.hom (Work.SSSR.normalizedChainComplexCoprodIso X M d).hom)
        ((ModuleCat.Hom.hom (Sigma.ι (fun _ : X.nonDegenerate d => M)
          ⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩)) m)
      = (ModuleCat.Hom.hom (X.ιNormalizedChainComplex (R := M)
          (Work.SSSR.nIndexBase X σ))) m := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, h2]
  have e3 : (ModuleCat.Hom.hom ((Work.SSSR.normalizedCoeffIsoIso X M).hom.f d))
        ((ModuleCat.Hom.hom (X.ιNormalizedChainComplex (R := M)
          (Work.SSSR.nIndexBase X σ))) m)
      = (ModuleCat.Hom.hom ((CategoryTheory.MonoidalCategory.leftUnitor M).inv ≫
          MonoidalCategoryStruct.whiskerRight
            (Sigma.ι (fun _ : X.nonDegenerate d => ModuleCat.of 𝕜 𝕜)
              ⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩) M)) m := by
    simp only [hcf]
    rw [h3]
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      hι (X.nonDegenerate d) ⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩]
    rfl
  have e4 : (ModuleCat.Hom.hom ((CategoryTheory.MonoidalCategory.leftUnitor M).inv ≫
          MonoidalCategoryStruct.whiskerRight
            (Sigma.ι (fun _ : X.nonDegenerate d => ModuleCat.of 𝕜 𝕜)
              ⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩) M)) m
      = TensorProduct.tmul 𝕜
          ((ModuleCat.Hom.hom (Sigma.ι (fun _ : X.nonDegenerate d => ModuleCat.of 𝕜 𝕜)
              ⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩)) 1) m := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    have hL : (ModuleCat.Hom.hom (CategoryTheory.MonoidalCategory.leftUnitor M).inv) m
        = 1 ⊗ₜ[𝕜] m := by
      rw [ModuleCat.hom_inv_leftUnitor]
      exact TensorProduct.lid_symm_apply m
    rw [hL]
    simp only [ModuleCat.hom_whiskerRight]
    exact LinearMap.rTensor_tmul (↑M)
      (ModuleCat.Hom.hom (Sigma.ι (fun _ : X.nonDegenerate d => ModuleCat.of 𝕜 𝕜)
        ⟨Work.SSSR.nIndexBase X σ, Work.SSSR.nIndexBase_mem X σ⟩)) m 1
  -- Step 4: assemble.
  rw [hcomp]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [e1, e2, e3, e4, h4]
  rfl

end Work.Pi6.MSS
