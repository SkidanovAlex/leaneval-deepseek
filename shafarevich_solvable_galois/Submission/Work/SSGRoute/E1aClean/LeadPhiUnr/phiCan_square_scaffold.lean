import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.extRes_PhiE_comp_khIota
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.he_of_hTheta
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.unitsToLocalUnits_eq_khIota_comp_theta
import Submission.Work.SSGRoute.E1aClean.h1locToClassRes
import Submission.Work.SSGRoute.E1aClean.phiUnrHelpers
import Submission.Work.SSGRoute.PT.E1aFinBox.levelChangeTransfer_e1cMap_eq_hensel

namespace Work.SSGRoute.E1aClean.LeadPhiUnr

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

attribute [local instance 10000] Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

theorem phiCan_square_main
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [hNorm : Normal ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)))
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      levelTwoGroupHom k Ω K A hA q hAq e
          (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z)
    (θ : Rep.res e.toMonoidHom
          (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) ⟶
        SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q))
    (hθ : ∀ u : (↥(henselOverDecomp k Ω K A))ˣ,
        Rep.Hom.hom θ (Additive.ofMul u) = Additive.ofMul
          (Units.map (decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom u))
    (hpush : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Function.Bijective ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (add_zero 1)))
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hl : SSGRoute.IsLocConstOn ⊤ b) :
    SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
      = Work.SSGRoute.E1aClean.phiCan p k Ω K ζ hζ hζK T hT A hA q hAq e hφres θ hpush E
          (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b) := by
  classical
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hAlg : IsAlgClosure ↥(decompField k Ω A) Ω := decompField_isAlgClosure_via k Ω K A rfl
  haveI hFd : FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_finiteDimensional k Ω K A
  haveI hGl : IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_isGalois k Ω K A
  haveI hChar : CharZero ↥(decompField k Ω A) := inferInstance
  haveI hFinD : Fintype ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    Fintype.ofFinite _
  haveI hFinK : Fintype (↥K ≃ₐ[k] ↥K) := inferInstance
  haveI hFinD' : Fintype (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
      ↥(henselOverDecomp k Ω K A)) := Fintype.ofFinite _
  have hfix : (decompField k Ω A).fixingSubgroup = SSGRoute.decomp k A :=
    decompField_fixingSubgroup_via k Ω K A rfl
  have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
    Work.SSGRoute.mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hl
  let 𝓔 : Rep.{0} Coeff (↥K ≃ₐ[k] ↥K) :=
    SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
  haveI hFin𝓔 : Finite (𝓔 : Type) := by
    change Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
    exact Work.SSGRoute.PT.finite_dualMod_tensor p E T
  haveI hModFin𝓔 : Module.Finite ℤ (𝓔 : Type) := Module.Finite.of_finite
  let Φd : E ≃+ Work.SSGRoute.homCoind k Ω K 𝓔 :=
    Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E
  have hΦ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Φd.toAddMonoidHom : E →+ Work.SSGRoute.homCoind k Ω K 𝓔) :=
    fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e
  have hΨ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Φd.symm.toAddMonoidHom :
        Work.SSGRoute.homCoind k Ω K 𝓔 →+ E) :=
    fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n
  rw [SSGRoute.SSGStage.extLoc_extToIdeles_eq]
  dsimp only [Work.SSGRoute.E1aClean.globalDictionaryCanon]
  rw [dif_pos hbZ]
  have hGDCval : Work.SSGRoute.E1aClean.globalDictEquivCanon p k Ω K ζ hζ hζK T hT E
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)
      = (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔).symm
          ((Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦ hΨ)
            (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)) := by
    simp only [Work.SSGRoute.E1aClean.globalDictEquivCanon, AddEquiv.trans_apply]
    rfl
  rw [hGDCval]
  have hbH : b ∈ SSGRoute.lcCocycles p k Ω K E (decompField k Ω A).fixingSubgroup :=
    ⟨(fun g _ h _ => hb g trivial h trivial),
     by obtain ⟨U, hUo, hU⟩ := hl; exact ⟨U, hUo, fun g _ u hu _ => hU g trivial u hu trivial⟩⟩
  unfold Work.SSGRoute.E1aClean.phiCan
  simp only [AddEquiv.trans_apply]
  rw [Work.SSGRoute.E1aClean.h1locSubgroupEqEquiv_toClass p k Ω K E hfix.symm b]
  rw [Work.SSGRoute.E1aClean.h1locEquivH1_toClass_eq_resH1 p k Ω K E
        (decompField k Ω A).fixingSubgroup (fun _ _ => rfl) b hbH hbZ]
  repeat rw [AddEquiv.trans_apply]
  let c₁ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K 𝓔)) :=
    Work.AbsoluteKummer.mapZ1 Φd.toAddMonoidHom
      (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e)
      ⟨b, hbZ⟩
  have hstep3 :
      (Work.SSGRoute.H1Equiv.h1AddEquiv (G := ↥((decompField k Ω A).fixingSubgroup)) Φd
        (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E
          (σ : Ω ≃ₐ[k] Ω) e)
        (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E
          (σ : Ω ≃ₐ[k] Ω) n))
      (Work.SSGRoute.PT.H2Fin.resH1 ((decompField k Ω A).fixingSubgroup) E
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩))
    = Work.SSGRoute.PT.H2Fin.resH1 ((decompField k Ω A).fixingSubgroup)
        (Work.SSGRoute.homCoind k Ω K 𝓔)
        (Work.SSGRoute.H1Equiv.h1AddEquiv (G := Ω ≃ₐ[k] Ω) Φd hΦ hΨ
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)) :=
    Work.SSGRoute.E1aClean.resH1_h1AddEquiv ((decompField k Ω A).fixingSubgroup) Φd hΦ
      (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E
        (σ : Ω ≃ₐ[k] Ω) e)
      hΨ
      (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E
        (σ : Ω ≃ₐ[k] Ω) n)
      (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)
  rw [hstep3]
  have hstep4 :
      (levelChangeTransferD p k Ω K A 𝓔 (levelTwoGroupHom k Ω K A hA q hAq e) hφres)
        (Work.SSGRoute.PT.H2Fin.resH1 ((decompField k Ω A).fixingSubgroup)
          (Work.SSGRoute.homCoind k Ω K 𝓔)
          (Work.SSGRoute.H1Equiv.h1AddEquiv (G := Ω ≃ₐ[k] Ω) Φd hΦ hΨ
            (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)))
    = levelChangeTransfer A 𝓔 (levelTwoGroupHom k Ω K A hA q hAq e) hφres
        (Work.SSGRoute.H1Equiv.h1AddEquiv (G := Ω ≃ₐ[k] Ω) Φd hΦ hΨ
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)) :=
    rfl
  rw [hstep4]
  let R₂ : Rep.{0} Coeff (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
      ↥(henselOverDecomp k Ω K A)) :=
    Rep.res e.symm.toMonoidHom (Rep.res
      (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype 𝓔)
  let c₂ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
      (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) R₂)) :=
    ⟨fun g => c₁.1 (AlgEquiv.restrictScalars k g),
      Work.SSGRoute.E1aClean.levelChange_mem_Z1 A 𝓔
        (levelTwoGroupHom k Ω K A hA q hAq e) hφres
        (Work.SSGRoute.E1aClean.restrictScalars_decompField_continuous A) c₁⟩
  let ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) 𝓔 :=
    Work.SSGRoute.ExtChain.E1cGeneric.liftOf (k := k) (Ω := Ω) (K := K) 𝓔 c₁
  have hñ : ∀ g : Ω ≃ₐ[k] Ω,
      Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) 𝓔 (c₁.1 g)
        = Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) 𝓔) ñ g := by
    intro g
    have hspec := congrFun (Work.SSGRoute.ExtChain.E1cGeneric.liftOf_spec
      (k := k) (Ω := Ω) (K := K) 𝓔 c₁) g
    rw [Work.GroupCohomology.d0_apply] at hspec
    rw [Work.GroupCohomology.d0_apply]
    exact hspec.symm
  have hmem : Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔 ñ
      ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.homCoind k Ω K
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) 𝓔)) := by
    rw [← Work.SSGRoute.ExtChain.E1cGeneric.d0_eq_zero_iff]
    funext g
    rw [Work.SSGRoute.ExtChain.E1cGeneric.d0_piH]
    show Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔
        (Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) 𝓔) ñ g) = 0
    rw [← hñ g, Work.SSGRoute.ExtChain.E1cGeneric.piH_iotaH]
  let y : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) 𝓔)
      (SSGRoute.PTExt.unitsK k K) 0 :=
    (Work.SSGRoute.ExtChain.E1cGeneric.PsiE (k := k) (Ω := Ω) (K := K)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) 𝓔)).symm
      ⟨Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔 ñ, hmem⟩
  have hy : (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔 ñ
        : Work.SSGRoute.homCoind k Ω K
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) 𝓔))
      = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) 𝓔) y) := by
    have h : Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) 𝓔) y
        = (⟨Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) 𝓔 ñ, hmem⟩ :
            ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
              (Work.SSGRoute.homCoind k Ω K
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) 𝓔)))) :=
      AddEquiv.apply_symm_apply _ _
    rw [h]
  let ñ₂ := levelTwoLift k Ω K A hA q hAq e 𝓔 ñ
  have hñ₂ : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      Work.SSGRoute.ExtChain.E1cGeneric.iotaH
          (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A)
          R₂ (c₂.1 g)
        = Work.GroupCohomology.d0 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := ↥(decompField k Ω A)) (Ω := Ω)
              (K := henselOverDecomp k Ω K A) R₂) ñ₂ g :=
    levelChange_lift_transport A 𝓔 (levelTwoGroupHom k Ω K A hA q hAq e) hφres c₁ ñ hñ
  have hmem₂ : Work.SSGRoute.ExtChain.E1cGeneric.piH
      (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂ ñ₂
      ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
          (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
              (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂)) := by
    rw [← Work.SSGRoute.ExtChain.E1cGeneric.d0_eq_zero_iff]
    funext g
    rw [Work.SSGRoute.ExtChain.E1cGeneric.d0_piH]
    show Work.SSGRoute.ExtChain.E1cGeneric.piH
        (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂
        (Work.GroupCohomology.d0 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := ↥(decompField k Ω A)) (Ω := Ω)
            (K := henselOverDecomp k Ω K A) R₂) ñ₂ g) = 0
    rw [← hñ₂ g, Work.SSGRoute.ExtChain.E1cGeneric.piH_iotaH]
  let y₂ : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
        (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂)
      (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) 0 :=
    (Work.SSGRoute.ExtChain.E1cGeneric.PsiE
      (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
        (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂)).symm
      ⟨Work.SSGRoute.ExtChain.E1cGeneric.piH
        (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂ ñ₂, hmem₂⟩
  have hy₂ : (Work.SSGRoute.ExtChain.E1cGeneric.piH
        (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂ ñ₂
        : Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
            (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂))
      = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
          (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A)
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
            (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂) y₂) := by
    have h : Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
        (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A)
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
          (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂) y₂
        = (⟨Work.SSGRoute.ExtChain.E1cGeneric.piH
            (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂ ñ₂,
            hmem₂⟩ :
            ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
              (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
                  (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂)))) :=
      AddEquiv.apply_symm_apply _ _
    rw [h]
  have hW : Work.SSGRoute.H1Equiv.h1AddEquiv (G := Ω ≃ₐ[k] Ω) Φd hΦ hΨ
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)
      = Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) 𝓔
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) 𝓔 y) := by
    rw [Work.SSGRoute.ExtChain.E1cGeneric.e1cMap_eq_H1π_of_cocycle_lift (k := k) (Ω := Ω)
      (K := K) 𝓔 c₁ ñ hñ y hy]
    show Work.AbsoluteKummer.mapH1 Φd.toAddMonoidHom hΦ
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)
      = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K 𝓔) c₁
    rw [Work.AbsoluteKummer.mapH1_H1π]
  have he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (x : ↥K),
      ((e τ) ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ : Ω)
        = ((τ : ↥K ≃ₐ[k] ↥K) x : Ω) :=
    he_of_hTheta k Ω K A hA q hAq e halg θ hθ
  have hglue : levelChangeTransfer A 𝓔 (levelTwoGroupHom k Ω K A hA q hAq e) hφres
        (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) 𝓔
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) 𝓔 y))
      = Work.SSGRoute.ExtChain.E1cGeneric.e1cMap
          (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE
            (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂ y₂) :=
    Work.SSGRoute.PT.E1aFinBox.levelChangeTransfer_e1cMap_eq_hensel_of_lift
      (k := k) (Ω := Ω) (K := K) A hA q hAq e he hφres 𝓔 c₁ ñ hñ c₂ hñ₂ y hy y₂ hy₂
  rw [hW, hglue]
  rw [show (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔).symm
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) 𝓔
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) 𝓔 y))
      = Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) 𝓔 y from
    AddEquiv.symm_apply_apply _ _]
  rw [show (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := ↥(decompField k Ω A)) (Ω := Ω)
        (K := henselOverDecomp k Ω K A) R₂).symm
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := ↥(decompField k Ω A)) (Ω := Ω)
        (K := henselOverDecomp k Ω K A) R₂
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := ↥(decompField k Ω A)) (Ω := Ω)
          (K := henselOverDecomp k Ω K A) R₂ y₂))
      = Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := ↥(decompField k Ω A)) (Ω := Ω)
          (K := henselOverDecomp k Ω K A) R₂ y₂ from
    AddEquiv.symm_apply_apply _ _]
  -- the crux, proved in `LeadPhiUnr/extRes_PhiE_comp_khIota`
  have hcrux : (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite q)).subtype
      (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) 𝓔 y)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (Work.SSGRoute.ExtChain.khIota (k := k) (Ω := Ω) (K := K) A q e he)) (add_zero 1)
    = Work.SSGRoute.E1aClean.extResEquivExplicit e
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype 𝓔)
        (Rep.res e.toMonoidHom
          (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)))
        ((Work.SSGRoute.E1aClean.res_comp_symm_self e
            (SSGRoute.PTExt.unitsK ↥(decompField k Ω A)
              ↥(henselOverDecomp k Ω K A))).symm ▸
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE
            (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A)
            (Rep.res e.symm.toMonoidHom
              (Rep.res (SSGRoute.PTExt.decompK (k := k)
                (NK.GlobalCFT.Place.ofFinite q)).subtype 𝓔)) y₂)) :=
    extRes_PhiE_comp_khIota k Ω K A hA q hAq e hφres halg he 𝓔 ñ y hy ñ₂ rfl y₂ hy₂
  have hmu := unitsToLocalUnits_eq_khIota_comp_theta k Ω K A hA q hAq e he halg θ hθ
  have hLHS : (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite q)).subtype
      (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) 𝓔 y)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofFinite q)))
      (add_zero 1)
    = ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype 𝓔)
        (add_zero 1))
        ((SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite q)).subtype
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) 𝓔 y)).comp
          (CategoryTheory.Abelian.Ext.mk₀
            (Work.SSGRoute.ExtChain.khIota (k := k) (Ω := Ω) (K := K) A q e he))
          (add_zero 1)) := by
    rw [hmu, ← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
      ← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
    rfl
  have hcast : (Eq.mp (congrArg (fun S => CategoryTheory.Abelian.Ext R₂
        (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) 1 ≃+
        CategoryTheory.Abelian.Ext R₂ S 1)
        (Work.SSGRoute.E1aClean.res_comp_symm_self e
          (SSGRoute.PTExt.unitsK ↥(decompField k Ω A)
            ↥(henselOverDecomp k Ω K A))).symm) (AddEquiv.refl _))
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE
          (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂ y₂)
      = (Work.SSGRoute.E1aClean.res_comp_symm_self e
          (SSGRoute.PTExt.unitsK ↥(decompField k Ω A)
            ↥(henselOverDecomp k Ω K A))).symm ▸
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE
          (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂ y₂) :=
    Work.SSGRoute.E1aClean.eq_mp_congrArg_refl_apply_ext _ _
  rw [hLHS, AddEquiv.ofBijective_apply, hcast, hcrux]

end Work.SSGRoute.E1aClean.LeadPhiUnr
