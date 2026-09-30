import Mathlib
import Submission.Work.SSSR.coprodShortComplex_homology
import Submission.Work.SSSR.serreE1CoefExplicit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits
noncomputable section

/-- **Explicit form of the isomorphism underlying `Work.SSSR.coprodShortComplex_homology`.**
The construction is the one already used inside that proof. -/
noncomputable def coprodShortComplexHomologyIso {C : Type*} [Category C] [Abelian C] {ι : Type}
    [HasColimitsOfShape (Discrete ι) C]
    [PreservesFiniteLimits (colim (J := Discrete ι) (C := C))]
    (S : ι → ShortComplex C) :
    (coprodShortComplex S).homology ≅ ∐ (fun i => (S i).homology) := by
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
  let hT : (coprodShortComplex S).LeftHomologyData := (coprodShortComplex S).leftHomologyData
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

/-- **Explicit form of `Work.SSSR.homology_sigma`.** -/
noncomputable def homology_sigmaIso {ι : Type} (F : ι → ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (∐ F).homology n ≅ ∐ (fun i => (F i).homology n) :=
  HomologicalComplex.homologyMapIso (coprodComplexIso F) n ≪≫
    coprodShortComplexHomologyIso (fun i => (F i).sc n)

end

end Work.SSSR
