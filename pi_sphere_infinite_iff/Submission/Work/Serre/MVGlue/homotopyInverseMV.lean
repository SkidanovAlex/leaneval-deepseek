import Mathlib
import Submission.Work.Serre.MVGlue.mvSetup
import Submission.Work.Cohomology.smallChainsHomotopyEquiv
import Submission.Work.Serre.MVGlue.smallToSingRetraction
import Submission.Work.Serre.MVGlue.smallInToSmall_emptyset
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.Cohomology.relComplex_empty_homology_iso

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre.MVGlue

noncomputable section

variable (X : TopCat) (U V : Set X)

/-- The explicit section of `HMV.mvPhi X ∅ U V` obtained by transporting the strict retraction of
`smallToSing U V` across the two comparison isomorphisms `smallChains U V ≅ relMVTopC X ∅ U V` and
`singularChains ℤ X ≅ relChains X ∅`. -/
theorem exists_mvPhi_section (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    ∃ ψ₀ : Work.Cohomology.relChains X (∅ : Set X) ⟶
        Work.Cohomology.relMVTopC X (∅ : Set X) U V,
      Work.Cohomology.HMV.mvPhi X (∅ : Set X) U V ≫ ψ₀ = 𝟙 _ := by
  obtain ⟨v, hv⟩ := smallToSingRetraction X U V hU hV hcov
  haveI hT : IsIso (cokernel.π (Work.Cohomology.inclChains X (∅ : Set X))) :=
    cokernel.π_of_zero (Work.Cohomology.inclChains_empty_eq_zero X)
  haveI hR : IsIso (cokernel.π (Work.Cohomology.smallInToSmall U V (∅ : Set X))) :=
    smallInToSmall_emptyset X U V
  refine ⟨inv (cokernel.π (Work.Cohomology.inclChains X (∅ : Set X))) ≫ v ≫
    cokernel.π (Work.Cohomology.smallInToSmall U V (∅ : Set X)), ?_⟩
  have hmv : Work.Cohomology.HMV.mvPhi X (∅ : Set X) U V
      = inv (cokernel.π (Work.Cohomology.smallInToSmall U V (∅ : Set X))) ≫
        Work.Cohomology.smallToSing U V ≫
        cokernel.π (Work.Cohomology.inclChains X (∅ : Set X)) := by
    have h := Work.Cohomology.HMV.mvPhi_comp X (∅ : Set X) U V
    have h2 : inv (cokernel.π (Work.Cohomology.smallInToSmall U V (∅ : Set X))) ≫
        (cokernel.π (Work.Cohomology.smallInToSmall U V (∅ : Set X)) ≫
          Work.Cohomology.HMV.mvPhi X (∅ : Set X) U V)
        = Work.Cohomology.HMV.mvPhi X (∅ : Set X) U V := by
      rw [IsIso.inv_hom_id_assoc]
    rw [← h2, h]
  rw [hmv]
  simp only [Category.assoc]
  have hM : Work.Cohomology.smallToSing U V ≫ v
      ≫ cokernel.π (Work.Cohomology.smallInToSmall U V (∅ : Set X))
      = cokernel.π (Work.Cohomology.smallInToSmall U V (∅ : Set X)) := by
    rw [← Category.assoc, hv, Category.id_comp]
  rw [IsIso.hom_inv_id_assoc, hM, IsIso.inv_hom_id]

/-- The comparison `zetaW` is an isomorphism of cochain complexes. -/
theorem isIso_zetaSmv_tau3 :
    IsIso (zetaSmv X (∅ : Set X) U V).τ₃ := by
  rw [zetaSmv_τ₃]
  have h : zetaW X (∅ : Set X) U V
      = (ThetaCmp (TopCat.of ↥(U ∩ V))
            (Work.Cohomology.interAU (∅ : Set X) (U ∩ V))).hom
        ≫ dqMap (Work.Cohomology.relMVUVPhi X (∅ : Set X) U V) := rfl
  rw [h]
  haveI : IsIso (Work.Cohomology.relMVUVPhi X (∅ : Set X) U V) :=
    (Work.Cohomology.hmv_isIso_eta X (∅ : Set X) U V).2.2
  haveI : IsIso (dqMap (Work.Cohomology.relMVUVPhi X (∅ : Set X) U V)) := isIso_dqMap _
  infer_instance

/-- The comparison `zetaMid` is an isomorphism of cochain complexes. -/
theorem isIso_zetaSmv_tau2 :
    IsIso (zetaSmv X (∅ : Set X) U V).τ₂ := by
  have hU' : IsIso (zetaU X (∅ : Set X) U V) := by
    have h : zetaU X (∅ : Set X) U V
        = (ThetaCmp (TopCat.of ↥U) (Work.Cohomology.interAU (∅ : Set X) U)).hom
          ≫ dqMap (Work.Cohomology.HMV.etaU (∅ : Set X) U V) := rfl
    rw [h]
    haveI : IsIso (Work.Cohomology.HMV.etaU (∅ : Set X) U V) :=
      (Work.Cohomology.hmv_isIso_eta X (∅ : Set X) U V).1
    haveI : IsIso (dqMap (Work.Cohomology.HMV.etaU (∅ : Set X) U V)) := isIso_dqMap _
    infer_instance
  have hV' : IsIso (zetaV X (∅ : Set X) U V) := by
    have h : zetaV X (∅ : Set X) U V
        = (ThetaCmp (TopCat.of ↥V) (Work.Cohomology.interAU (∅ : Set X) V)).hom
          ≫ dqMap (Work.Cohomology.HMV.etaV (∅ : Set X) U V) := rfl
    rw [h]
    haveI : IsIso (Work.Cohomology.HMV.etaV (∅ : Set X) U V) :=
      (Work.Cohomology.hmv_isIso_eta X (∅ : Set X) U V).2.1
    haveI : IsIso (dqMap (Work.Cohomology.HMV.etaV (∅ : Set X) U V)) := isIso_dqMap _
    infer_instance
  haveI : IsIso (biprod.map (zetaU X (∅ : Set X) U V) (zetaV X (∅ : Set X) U V)) := by
    have h : biprod.map (zetaU X (∅ : Set X) U V) (zetaV X (∅ : Set X) U V)
        = (biprod.mapIso (asIso (zetaU X (∅ : Set X) U V))
            (asIso (zetaV X (∅ : Set X) U V))).hom := by
      rw [biprod.mapIso_hom, asIso_hom, asIso_hom]
    rw [h]
    exact Iso.isIso_hom _
  rw [zetaSmv_τ₂]
  have h : zetaMid X (∅ : Set X) U V
      = biprod.map (zetaU X (∅ : Set X) U V) (zetaV X (∅ : Set X) U V)
        ≫ (dqBiprodIso (Work.Cohomology.relMVUU X (∅ : Set X) U V)
            (Work.Cohomology.relMVVV X (∅ : Set X) U V)).inv := rfl
  rw [h]
  infer_instance

theorem homotopyInverseMV (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    ∃ η : Work.Serre.dqShort X (∅ : Set X) U V ⟶ Work.Serre.MVGlue.Smv X (∅ : Set X) U V,
      (∀ k : ℕ,
        CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap η.τ₁ k)
            (HomologicalComplex.homologyMap (Work.Serre.MVGlue.zetaSmv X (∅ : Set X) U V).τ₁ k)
          = CategoryTheory.CategoryStruct.id
              ((Work.Serre.dqShort X (∅ : Set X) U V).X₁.homology k)
        ∧ CategoryTheory.CategoryStruct.comp
            (HomologicalComplex.homologyMap (Work.Serre.MVGlue.zetaSmv X (∅ : Set X) U V).τ₁ k)
            (HomologicalComplex.homologyMap η.τ₁ k)
          = CategoryTheory.CategoryStruct.id
              ((Work.Serre.MVGlue.Smv X (∅ : Set X) U V).X₁.homology k))
      ∧ (∀ k : ℕ,
        CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap η.τ₃ k)
            (HomologicalComplex.homologyMap (Work.Serre.MVGlue.zetaSmv X (∅ : Set X) U V).τ₃ k)
          = CategoryTheory.CategoryStruct.id
              ((Work.Serre.dqShort X (∅ : Set X) U V).X₃.homology k)
        ∧ CategoryTheory.CategoryStruct.comp
            (HomologicalComplex.homologyMap (Work.Serre.MVGlue.zetaSmv X (∅ : Set X) U V).τ₃ k)
            (HomologicalComplex.homologyMap η.τ₃ k)
          = CategoryTheory.CategoryStruct.id
              ((Work.Serre.MVGlue.Smv X (∅ : Set X) U V).X₃.homology k)) := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_mvPhi_section X U V hU hV hcov
  haveI hZ2 : IsIso (zetaSmv X (∅ : Set X) U V).τ₂ := isIso_zetaSmv_tau2 X U V
  haveI hZ3 : IsIso (zetaSmv X (∅ : Set X) U V).τ₃ := isIso_zetaSmv_tau3 X U V
  -- the first component is a strict section of `zetaSmv.τ₁`
  have hτ₁ : (dqMap ψ₀ ≫ (ThetaCmp X (∅ : Set X)).inv) ≫ (zetaSmv X (∅ : Set X) U V).τ₁
      = 𝟙 _ := by
    rw [zetaSmv_τ₁]
    show (dqMap ψ₀ ≫ (ThetaCmp X (∅ : Set X)).inv) ≫
      ((ThetaCmp X (∅ : Set X)).hom
        ≫ dqMap (Work.Cohomology.HMV.mvPhi X (∅ : Set X) U V)) = 𝟙 _
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← dqMap_comp, hψ₀, dqMap_id]
  -- the middle and last components of `zetaSmv`
  have hTf : (Smv X (∅ : Set X) U V).f
      = ((zetaSmv X (∅ : Set X) U V).τ₁ ≫ (dqShort X (∅ : Set X) U V).f)
        ≫ inv (zetaSmv X (∅ : Set X) U V).τ₂ := by
    refine (IsIso.eq_comp_inv (α := (zetaSmv X (∅ : Set X) U V).τ₂)).mpr ?_
    exact (zetaSmv X (∅ : Set X) U V).comm₁₂ |>.symm
  have hTg : (Smv X (∅ : Set X) U V).g
      = ((zetaSmv X (∅ : Set X) U V).τ₂ ≫ (dqShort X (∅ : Set X) U V).g)
        ≫ inv (zetaSmv X (∅ : Set X) U V).τ₃ := by
    refine (IsIso.eq_comp_inv (α := (zetaSmv X (∅ : Set X) U V).τ₃)).mpr ?_
    exact (zetaSmv X (∅ : Set X) U V).comm₂₃ |>.symm
  -- the two squares
  have hA : (dqMap ψ₀ ≫ (ThetaCmp X (∅ : Set X)).inv) ≫ (Smv X (∅ : Set X) U V).f
      = (dqShort X (∅ : Set X) U V).f ≫ inv (zetaSmv X (∅ : Set X) U V).τ₂ := by
    rw [hTf, ← Category.assoc, ← Category.assoc, hτ₁, Category.id_comp]
  have hB : inv (zetaSmv X (∅ : Set X) U V).τ₂ ≫ (Smv X (∅ : Set X) U V).g
      = (dqShort X (∅ : Set X) U V).g ≫ inv (zetaSmv X (∅ : Set X) U V).τ₃ := by
    rw [hTg, ← Category.assoc, IsIso.inv_hom_id_assoc]
  let η : Work.Serre.dqShort X (∅ : Set X) U V ⟶ Smv X (∅ : Set X) U V :=
    ShortComplex.homMk (dqMap ψ₀ ≫ (ThetaCmp X (∅ : Set X)).inv)
      (inv (zetaSmv X (∅ : Set X) U V).τ₂) (inv (zetaSmv X (∅ : Set X) U V).τ₃) hA hB
  have hη₁ : η.τ₁ = dqMap ψ₀ ≫ (ThetaCmp X (∅ : Set X)).inv := rfl
  have hη₃ : η.τ₃ = inv (zetaSmv X (∅ : Set X) U V).τ₃ := rfl
  refine ⟨η, ?_, ?_⟩
  · intro k
    refine ⟨?_, ?_⟩
    · show HomologicalComplex.homologyMap η.τ₁ k
          ≫ HomologicalComplex.homologyMap (zetaSmv X (∅ : Set X) U V).τ₁ k = 𝟙 _
      rw [hη₁, ← HomologicalComplex.homologyMap_comp, hτ₁, HomologicalComplex.homologyMap_id]
    · have h1 : HomologicalComplex.homologyMap η.τ₁ k
          ≫ HomologicalComplex.homologyMap (zetaSmv X (∅ : Set X) U V).τ₁ k = 𝟙 _ := by
        rw [hη₁, ← HomologicalComplex.homologyMap_comp, hτ₁, HomologicalComplex.homologyMap_id]
      haveI : IsIso (HomologicalComplex.homologyMap (zetaSmv X (∅ : Set X) U V).τ₁ k) :=
        isIso_zetaSmv_τ₁ X (∅ : Set X) U V hU hV hcov k
      have h2 : HomologicalComplex.homologyMap η.τ₁ k
          = CategoryTheory.inv
              (HomologicalComplex.homologyMap (zetaSmv X (∅ : Set X) U V).τ₁ k) :=
        IsIso.eq_inv_of_inv_hom_id h1
      rw [h2, IsIso.hom_inv_id]
  · intro k
    refine ⟨?_, ?_⟩
    · show HomologicalComplex.homologyMap η.τ₃ k
          ≫ HomologicalComplex.homologyMap (zetaSmv X (∅ : Set X) U V).τ₃ k = 𝟙 _
      rw [hη₃, ← HomologicalComplex.homologyMap_comp, IsIso.inv_hom_id,
        HomologicalComplex.homologyMap_id]
    · show HomologicalComplex.homologyMap (zetaSmv X (∅ : Set X) U V).τ₃ k
          ≫ HomologicalComplex.homologyMap η.τ₃ k = 𝟙 _
      rw [hη₃, ← HomologicalComplex.homologyMap_comp, IsIso.hom_inv_id,
        HomologicalComplex.homologyMap_id]

end

end Work.Serre.MVGlue
