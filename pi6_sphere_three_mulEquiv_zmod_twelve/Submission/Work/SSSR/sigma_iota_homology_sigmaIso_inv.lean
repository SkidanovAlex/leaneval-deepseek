import Mathlib
import Submission.Work.SSSR.homology_sigmaExplicit
import Submission.Work.SSSR.coprodComplex_iso
import Submission.Work.SSSR.coprodShortComplex_homology
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits
noncomputable section

abbrev coprodShortComplexA {ι : Type} (S : ι → ShortComplex (ModuleCat R)) :
    ShortComplex (ModuleCat R) :=
  { X₁ := ∐ (fun i => (S i).X₁)
    X₂ := ∐ (fun i => (S i).X₂)
    X₃ := ∐ (fun i => (S i).X₃)
    f := Limits.Sigma.map (fun i => (S i).f)
    g := Limits.Sigma.map (fun i => (S i).g)
    zero := by
      rw [Sigma.map_comp']
      have h : (fun i => (S i).f ≫ (S i).g) = (fun i => (0 : (S i).X₁ ⟶ (S i).X₃)) :=
        funext fun i => (S i).zero
      rw [h, Sigma.map_zero'] }

abbrev eKA {ι : Type} (S : ι → ShortComplex (ModuleCat R)) :
    (∐ fun j => (S j).leftHomologyData.K) ≅ (coprodShortComplexA S).leftHomologyData.K :=
  ((isLimit_sigmaMap_kernelFork (fun j => (S j).g) (fun j => (S j).leftHomologyData.i)
      (fun j => (S j).leftHomologyData.wi) (fun j => (S j).leftHomologyData.hi)
      (sigmaMap_kernel_zero' (fun j => (S j).g) (fun j => (S j).leftHomologyData.i)
        (fun j => (S j).leftHomologyData.wi))).conePointUniqueUpToIso
      (coprodShortComplexA S).leftHomologyData.hi)

def shortCoprodInjA {ι : Type} (S : ι → ShortComplex (ModuleCat R)) (i : ι) :
    S i ⟶ coprodShortComplexA S where
  τ₁ := Sigma.ι (fun j => (S j).X₁) i
  τ₂ := Sigma.ι (fun j => (S j).X₂) i
  τ₃ := Sigma.ι (fun j => (S j).X₃) i
  comm₁₂ := Sigma.ι_map (fun j => (S j).f) i
  comm₂₃ := Sigma.ι_map (fun j => (S j).g) i

def myCoprodShortComplexHomologyIso {ι : Type} (S : ι → ShortComplex (ModuleCat R)) :
    (coprodShortComplexA S).homology ≅ ∐ (fun i => (S i).homology) := by
  classical
  let h : ∀ i, (S i).LeftHomologyData := fun i => (S i).leftHomologyData
  have hk : ∀ i, (h i).i ≫ (S i).g = 0 := fun i => (h i).wi
  have hl : ∀ i, (S i).f ≫ (S i).g = 0 := fun i => (S i).zero
  have hk' : Limits.Sigma.map (fun i => (h i).i) ≫ Limits.Sigma.map (fun i => (S i).g) = 0 :=
    sigmaMap_kernel_zero' (fun i => (S i).g) (fun i => (h i).i) hk
  have hl' : Limits.Sigma.map (fun i => (S i).f) ≫ Limits.Sigma.map (fun i => (S i).g) = 0 :=
    sigmaMap_kernel_zero' (fun i => (S i).g) (fun i => (S i).f) hl
  have hlim : IsLimit (KernelFork.ofι (Limits.Sigma.map (fun i => (h i).i)) hk') :=
    isLimit_sigmaMap_kernelFork (fun i => (S i).g) (fun i => (h i).i) hk
      (fun i => (h i).hi) hk'
  let hT : (coprodShortComplexA S).LeftHomologyData := (coprodShortComplexA S).leftHomologyData
  let eK : (∐ fun i => (h i).K) ≅ hT.K :=
    IsLimit.conePointUniqueUpToIso
      (s := KernelFork.ofι (Limits.Sigma.map (fun i => (h i).i)) hk')
      (t := KernelFork.ofι hT.i hT.wi) hlim hT.hi
  have eK_i : eK.hom ≫ hT.i = Limits.Sigma.map (fun i => (h i).i) :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (s := KernelFork.ofι (Limits.Sigma.map (fun i => (h i).i)) hk')
      (t := KernelFork.ofι hT.i hT.wi) hlim hT.hi WalkingParallelPair.zero
  have hf' : hT.f' = Limits.Sigma.map (fun i => (h i).f') ≫ eK.hom :=
    lift_sigmaMap_eq_sigmaMap_lift (fun i => (S i).g) (fun i => (h i).i) (fun i => (S i).f)
      hk hl (fun i => (h i).hi) hk' hl' hlim hT.wi hT.hi eK eK_i
  have hc' : Limits.Sigma.map (fun i => (h i).f') ≫ Limits.Sigma.map (fun i => (h i).π) = 0 :=
    sigmaMap_cokernel_zero' (fun i => (h i).f') (fun i => (h i).π) (fun i => (h i).f'_π)
  have hco : IsColimit (CokernelCofork.ofπ (Limits.Sigma.map (fun i => (h i).π)) hc') :=
    isColimit_sigmaMap_cokernelCofork (fun i => (h i).f') (fun i => (h i).π)
      (fun i => (h i).f'_π) (fun i => (h i).hπ) hc'
  exact (hT.homologyIso).trans
    (((IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel hT.f') hT.hπ).symm).trans
      ((cokernel.mapIso hT.f' (Limits.Sigma.map (fun i => (h i).f')) (Iso.refl _) eK.symm
        (comp_inv_eq_id_comp hT.f' (Limits.Sigma.map (fun i => (h i).f')) eK hf')).trans
        ((IsColimit.coconePointUniqueUpToIso
          (cokernelIsCokernel (Limits.Sigma.map (fun i => (h i).f'))) hco).trans
          (Sigma.mapIso (fun i => ((h i).homologyIso).symm)))))

theorem myCoprodShortComplexHomologyIso_eq {ι : Type} (S : ι → ShortComplex (ModuleCat R)) :
    myCoprodShortComplexHomologyIso S = coprodShortComplexHomologyIso S := rfl

lemma cokernel.π_comp_map_assoc {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Z W : C} (f : X ⟶ Y) [HasCokernel f] (f' : Z ⟶ W) [HasCokernel f']
    (p : X ⟶ Z) (q : Y ⟶ W) (w : f ≫ q = p ≫ f') {T : C} (Y' : cokernel f' ⟶ T) :
    cokernel.π f ≫ (cokernel.map f f' p q w ≫ Y') = q ≫ cokernel.π f' ≫ Y' := by
  rw [← Category.assoc,
    show cokernel.map f f' p q w = cokernel.desc f (q ≫ cokernel.π f') _ from rfl,
    cokernel.π_desc, Category.assoc]

theorem coprodShortComplexHomologyIsoA_comp_ι {ι : Type} (S : ι → ShortComplex (ModuleCat R))
    (i : ι) :
    ShortComplex.homologyMap (shortCoprodInjA S i) ≫ (myCoprodShortComplexHomologyIso S).hom
      = Sigma.ι (fun j => (S j).homology) i := by
  simp only [myCoprodShortComplexHomologyIso, Iso.trans_hom]
  rw [← Category.assoc]
  rw [ShortComplex.LeftHomologyMapData.homologyMap_comm (shortCoprodInjA S i)
        (ShortComplex.leftHomologyMapData (shortCoprodInjA S i) (S i).leftHomologyData
          (coprodShortComplexA S).leftHomologyData)]
  have hcyc : (ShortComplex.leftHomologyMapData (shortCoprodInjA S i) (S i).leftHomologyData
        (coprodShortComplexA S).leftHomologyData).φK
      = Sigma.ι (fun j => (S j).leftHomologyData.K) i ≫ (eKA S).hom := by
    apply (cancel_mono (coprodShortComplexA S).leftHomologyData.i).mp
    rw [ShortComplex.LeftHomologyMapData.commi]
    rw [show (shortCoprodInjA S i).τ₂ = Sigma.ι (fun j => (S j).X₂) i from rfl]
    rw [Category.assoc]
    have eK_iA : (eKA S).hom ≫ (coprodShortComplexA S).leftHomologyData.i
        = Limits.Sigma.map (fun j => (S j).leftHomologyData.i) := by
      have h := IsLimit.conePointUniqueUpToIso_hom_comp
        (isLimit_sigmaMap_kernelFork (fun j => (S j).g) (fun j => (S j).leftHomologyData.i)
          (fun j => (S j).leftHomologyData.wi) (fun j => (S j).leftHomologyData.hi)
          (sigmaMap_kernel_zero' (fun j => (S j).g) (fun j => (S j).leftHomologyData.i)
            (fun j => (S j).leftHomologyData.wi)))
        (coprodShortComplexA S).leftHomologyData.hi WalkingParallelPair.zero
      simpa using h
    rw [eK_iA, Sigma.ι_map]
  have hcycq : ∀ {Z : ModuleCat R} (Y : (∐ fun j => (S j).leftHomologyData.K) ⟶ Z),
      (ShortComplex.leftHomologyMapData (shortCoprodInjA S i) (S i).leftHomologyData
        (coprodShortComplexA S).leftHomologyData).φK ≫ ((eKA S).symm.hom ≫ Y)
      = Sigma.ι (fun j => (S j).leftHomologyData.K) i ≫ Y := by
    intro Z Y
    rw [hcyc, Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc]
  have hB : (coprodShortComplexA S).leftHomologyData.π ≫
        ((cokernelIsCokernel (coprodShortComplexA S).leftHomologyData.f').coconePointUniqueUpToIso
            (coprodShortComplexA S).leftHomologyData.hπ).symm.hom
      = cokernel.π (coprodShortComplexA S).leftHomologyData.f' := by
    rw [Iso.symm_hom]
    exact IsColimit.comp_coconePointUniqueUpToIso_inv
      (cokernelIsCokernel (coprodShortComplexA S).leftHomologyData.f')
      (coprodShortComplexA S).leftHomologyData.hπ WalkingParallelPair.one
  have hBq : ∀ {Z : ModuleCat R} (Y : cokernel (coprodShortComplexA S).leftHomologyData.f' ⟶ Z),
      (coprodShortComplexA S).leftHomologyData.π ≫
        (((cokernelIsCokernel (coprodShortComplexA S).leftHomologyData.f').coconePointUniqueUpToIso
            (coprodShortComplexA S).leftHomologyData.hπ).symm.hom ≫ Y)
      = cokernel.π (coprodShortComplexA S).leftHomologyData.f' ≫ Y := by
    intro Z Y
    rw [← Category.assoc, hB]
  have hc' : Limits.Sigma.map (fun j => (S j).leftHomologyData.f') ≫
      Limits.Sigma.map (fun j => (S j).leftHomologyData.π) = 0 :=
    sigmaMap_cokernel_zero' (fun j => (S j).leftHomologyData.f') (fun j => (S j).leftHomologyData.π)
      (fun j => (S j).leftHomologyData.f'_π)
  have hD : cokernel.π (Limits.Sigma.map (fun j => (S j).leftHomologyData.f')) ≫
        ((cokernelIsCokernel (Limits.Sigma.map fun j => (S j).leftHomologyData.f')).coconePointUniqueUpToIso
            (isColimit_sigmaMap_cokernelCofork (fun j => (S j).leftHomologyData.f')
              (fun j => (S j).leftHomologyData.π) (fun j => (S j).leftHomologyData.f'_π)
              (fun j => (S j).leftHomologyData.hπ) hc')).hom
      = Limits.Sigma.map (fun j => (S j).leftHomologyData.π) := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (Limits.Sigma.map fun j => (S j).leftHomologyData.f'))
      (isColimit_sigmaMap_cokernelCofork (fun j => (S j).leftHomologyData.f')
        (fun j => (S j).leftHomologyData.π) (fun j => (S j).leftHomologyData.f'_π)
        (fun j => (S j).leftHomologyData.hπ) hc')
      WalkingParallelPair.one
  have e3 : (S i).leftHomologyData.homologyIso.hom ≫
        Sigma.ι (fun j => (S j).leftHomologyData.H) i ≫
          (Sigma.mapIso fun j => (S j).leftHomologyData.homologyIso.symm).hom
      = Sigma.ι (fun j => (S j).homology) i := by
    rw [Sigma.ι_mapIso_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  rw [← e3]
  simp only [Category.assoc]
  apply (cancel_epi (S i).leftHomologyData.homologyIso.hom).mpr
  simp only [← Category.assoc]
  apply (cancel_mono (Sigma.mapIso fun j => (S j).leftHomologyData.homologyIso.symm).hom).mpr
  apply (cancel_epi (S i).leftHomologyData.π).mp
  simp only [← Category.assoc]
  rw [ShortComplex.LeftHomologyMapData.commπ]
  simp only [Category.assoc]
  rw [hBq]
  rw [cokernel.mapIso_hom]
  rw [cokernel.π_comp_map_assoc]
  rw [hD]
  rw [hcycq]
  rw [Sigma.ι_map]



theorem sigma_iota_homology_sigmaIso_inv {ι : Type} (F : ι → ChainComplex (ModuleCat R) ℕ)
    (n : ℕ) (i : ι) :
    Sigma.ι (fun i => (F i).homology n) i ≫ (homology_sigmaIso F n).inv
      = HomologicalComplex.homologyMap (Sigma.ι F i) n := by
  have hkey : ShortComplex.homologyMap (shortCoprodInjA (fun j => (F j).sc n) i)
      = HomologicalComplex.homologyMap (coprodComplexInj F i) n := rfl
  have hfam : Sigma.ι (fun i => (F i).homology n) i
      = Sigma.ι (fun j => ((F j).sc n).homology) i := rfl
  have hsig : Sigma.ι F i ≫ (coprodComplexIso F).hom = coprodComplexInj F i :=
    IsColimit.comp_coconePointUniqueUpToIso_inv (coprodComplex_isColimit F)
      (colimit.isColimit (Discrete.functor F)) (Discrete.mk i)
  have hsig' : Sigma.ι F i = coprodComplexInj F i ≫ (coprodComplexIso F).inv := by
    rw [← hsig, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hGinv : Sigma.ι (fun j => ((F j).sc n).homology) i ≫
      (myCoprodShortComplexHomologyIso (fun j => (F j).sc n)).inv
      = ShortComplex.homologyMap (shortCoprodInjA (fun j => (F j).sc n) i) := by
    have h := coprodShortComplexHomologyIsoA_comp_ι (fun j => (F j).sc n) i
    calc Sigma.ι (fun j => ((F j).sc n).homology) i ≫
          (myCoprodShortComplexHomologyIso (fun j => (F j).sc n)).inv
        = (ShortComplex.homologyMap (shortCoprodInjA (fun j => (F j).sc n) i) ≫
            (myCoprodShortComplexHomologyIso (fun j => (F j).sc n)).hom) ≫
            (myCoprodShortComplexHomologyIso (fun j => (F j).sc n)).inv := by rw [h]
      _ = ShortComplex.homologyMap (shortCoprodInjA (fun j => (F j).sc n) i) := by
            rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [show (homology_sigmaIso F n).inv
      = (coprodShortComplexHomologyIso (fun j => (F j).sc n)).inv ≫
        (HomologicalComplex.homologyMapIso (coprodComplexIso F) n).inv from rfl]
  rw [← myCoprodShortComplexHomologyIso_eq]
  rw [HomologicalComplex.homologyMapIso_inv]
  rw [hfam]
  rw [← Category.assoc, hGinv, hkey]
  rw [hsig', HomologicalComplex.homologyMap_comp]

end

end Work.SSSR
