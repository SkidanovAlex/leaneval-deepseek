import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.archCruxLinkedGen
import Submission.Work.SSGRoute.PT.decompK_linked
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (α) for `archimedeanDictNonsplit`: a coboundary on `⟨c⟩` localises to zero

If a global locally constant `1`-cocycle `b` restricts to a coboundary on the involution group
`⟨c⟩`, then the localisation of its canonical global dictionary class at the archimedean place `w`
vanishes.  This is the "(H) ⟹ (C)" direction of the archimedean comparison square; it is the
hypothesis of `archCruxA_gen_linked` once the `E1c` class of the dictionary class is identified.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- **(α).** -/
theorem archDict_coboundary_imp_localZero_own (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ)
    (hwinf : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥)
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b)
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    SSGRoute.PTExt.extLoc (k := k) w
      (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0 := by
  classical
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI hMfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  haveI hMfinZ : Module.Finite ℤ (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
    Module.Finite.of_finite
  haveI : Module.Finite ℤ (Eprime p k Ω K T E).V := hMfinZ
  -- the class of `b`
  have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
    Work.SSGRoute.mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hl
  -- the coefficient representation and the global dictionary class
  let 𝓔 : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) := Eprime p k Ω K T E
  let Φd : E ≃+ Work.SSGRoute.homCoind k Ω K 𝓔 :=
    Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E
  have hΦ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.toAddMonoidHom :=
    fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e
  have hΨ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.symm.toAddMonoidHom :=
    fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n
  have hdict : Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b
      = Work.SSGRoute.E1aClean.globalDictEquivCanon p k Ω K ζ hζ hζK T hT E
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) := by
    dsimp only [Work.SSGRoute.E1aClean.globalDictionaryCanon]
    exact dif_pos hbZ
  have hcls : Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) 𝓔
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)
      = (Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦ hΨ)
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) := by
    rw [hdict]
    dsimp only [Work.SSGRoute.E1aClean.globalDictEquivCanon,
      Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv,
      Work.SSGRoute.H1Equiv.h1AddEquiv]
    rw [AddEquiv.trans_apply]
    change (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔)
        ((Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔).symm
          ((Work.AbsoluteKummer.mapH1 Φd.toAddMonoidHom hΦ)
            (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)))
      = (Work.AbsoluteKummer.mapH1 Φd.toAddMonoidHom hΦ)
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)
    exact AddEquiv.apply_symm_apply _ _
  -- the restriction of the `E1c` class to `⟨c⟩` vanishes
  have hres : Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers c)
      (Work.SSGRoute.homCoind k Ω K 𝓔)
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) 𝓔
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0 := by
    rw [hcls]
    change (Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers c) (Work.SSGRoute.homCoind k Ω K 𝓔))
        ((Work.AbsoluteKummer.mapH1 Φd.toAddMonoidHom hΦ)
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)) = 0
    rw [resH1_mapH1 (Nsub := Subgroup.zpowers c) (θ := Φd.toAddMonoidHom) (hθ := hΦ)
      (hθ' := fun σ e => hΦ (σ : Ω ≃ₐ[k] Ω) e)]
    rw [show Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers c) E
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) = 0 from by
      rw [Work.SSGRoute.PT.H2Fin.resH1_H1π, Work.AbsoluteKummer.H1π_eq_zero_iff]
      exact resZ1_mem_absB1_of_isCoboundaryOn (Subgroup.zpowers c) b hbZ hcob]
    rw [map_zero]
  -- the place, as an infinite place
  set w' : NumberField.InfinitePlace ↥K :=
    NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)) with hw'def
  have hw' : w = NK.GlobalCFT.Place.ofInfinite w' := hw
  have hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w') ≤
      (Subgroup.zpowers c).map (SSGRoute.res k K) := by
    rw [hw'def]
    exact le_of_eq (Work.SSGRoute.PT.decompK_linked k Ω K c hc2 hc1 φ hlink)
  have hne' : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w') ≠ ⊥ := by
    rw [← hw']; exact hne
  -- the crux, in the two possible readings of the place `w'`
  have hcrux : (SSGRoute.PTExt.extRes
        (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w')).subtype
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofInfinite w')))
      (add_zero 1) = 0 := by
    rcases NumberField.InfinitePlace.embedding_mk_eq (φ.comp (algebraMap ↥K Ω)) with hcase | hcase
    · exact archCruxA_gen_linked (k := k) (Ω := Ω) (K := K) w' c hc2 φ
        (by intro y; rw [hw'def, hcase]; rfl) hlink hle hne' 𝓔 _ hres
    · refine archCruxA_gen_linked (k := k) (Ω := Ω) (K := K) w' c hc2
        (NumberField.ComplexEmbedding.conjugate φ) ?_ ?_ hle hne' 𝓔 _ hres
      · intro y
        rw [hw'def, hcase]
        rfl
      · intro y
        have h1 : (NumberField.ComplexEmbedding.conjugate φ) (c y)
            = starRingEnd ℂ (φ (c y)) := by
          simp [NumberField.ComplexEmbedding.conjugate]
        have h2 : (NumberField.ComplexEmbedding.conjugate φ) y
            = starRingEnd ℂ (φ y) := by
          simp [NumberField.ComplexEmbedding.conjugate]
        rw [h1, h2, hlink y]
  -- conclude
  rw [Work.SSGRoute.SSGStage.extLoc_extToIdeles_eq (k := k) (K := ↥K) w
    (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)]
  rw [hw]
  exact hcrux

end

end Work.SSGRoute.ArchDictionary
