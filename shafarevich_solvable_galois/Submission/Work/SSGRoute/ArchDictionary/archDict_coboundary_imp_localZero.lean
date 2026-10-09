import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.Defs
import Submission.Work.SSGRoute.ArchDictionary.archCruxLinkedGen
import Submission.Work.SSGRoute.PT.decompK_linked
import Submission.Work.SSGRoute.PT.e1a_localComparison_bricks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (α) for `archimedeanDictNonsplit`: a coboundary on `⟨c⟩` localises to zero

If a global locally constant `1`-cocycle `b` restricts to a coboundary on the involution group
`⟨c⟩`, then the localisation of its canonical global dictionary class at the archimedean place `w`
vanishes.  This is the "(H) ⟹ (C)" direction of the archimedean comparison square; it supplies the
hypothesis `hres` of `archCruxA_gen_linked` once the `E1c` class of the dictionary class is
identified with the class of `b`.

## Route

1. `E1cGeneric.e1cMap` of the canonical global dictionary class of `b` is
   `h1AddEquiv Φ_d (H¹π b)`, where `Φ_d = e1aCoeffNat` is the canonical identification
   `E ≃+ Hom_ℤ(E',Ωˣ)`;
2. its restriction to `⟨c⟩` therefore vanishes, because `b` is a coboundary on `⟨c⟩`
   (`resH1_mapH1` + `resZ1_mem_absB1_of_isCoboundaryOn`);
3. `archCruxA_gen_linked` (the archimedean crux with an explicit seam `φ : Ω →+* ℂ`) then kills
   `(extRes_{D_w} ·) ∘ mk₀(unitsToLocalUnits)`;
4. `extLoc_extToIdeles_eq` converts this back into `extLoc_w ∘ extToIdeles = 0`.

The place `w` is `mk (φ|_K)`; since `InfinitePlace.embedding` is only a *choice* of representative
of the conjugacy class defining the place (`InfinitePlace.embedding_mk_eq`), the seam is either `φ`
or its complex conjugate, and the crux is invoked in the corresponding case.

## Note on the statement

As filed, the `globalDictionaryCanon` of the conclusion was written without its explicit
`K`-argument (`globalDictionaryCanon p k Ω ζ …`), which does not elaborate: the fourth explicit
argument of that function is `K : IntermediateField k Ω`.  The statement below is the unique
well-typed reading — exactly the statement of the delegation file
`Work.SSGRoute.ArchDictionary._check_deleg.archDict_coboundary_imp_localZero`, and the shape every
other statement of this directory uses.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- **(α).**  A cocycle which is a coboundary on the involution group `⟨c⟩` has vanishing
archimedean localisation. -/
theorem archDict_coboundary_imp_localZero (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
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
  -- the coefficient module `E' = DualMod p (E ⊗ T)` is finite, hence `ℤ`-finite
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI hMfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  haveI hMfinZ : Module.Finite ℤ (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
    Module.Finite.of_finite
  haveI hMfinZ' : Module.Finite ℤ (Eprime p k Ω K T E).V := hMfinZ
  -- the class of `b`
  have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
    Work.SSGRoute.mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hl
  -- the coefficient representation and the canonical coefficient identification
  let 𝓔 : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) := Eprime p k Ω K T E
  let Φd : E ≃+ Work.SSGRoute.homCoind k Ω K 𝓔 :=
    Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E
  have hΦ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.toAddMonoidHom :=
    fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e
  have hΨ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.symm.toAddMonoidHom :=
    fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n
  -- **Step 1**: the `E1c` class of the dictionary class is the canonical one of `b`
  -- (the right-hand side is `h1AddEquiv Φd hΦ hΨ` of the class of `b`, definitionally)
  have hcls : Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) 𝓔
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)
      = (Work.AbsoluteKummer.mapH1 Φd.toAddMonoidHom hΦ)
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) := by
    rw [show Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b
        = Work.SSGRoute.E1aClean.globalDictEquivCanon p k Ω K ζ hζ hζK T hT E
            (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) from by
      dsimp only [Work.SSGRoute.E1aClean.globalDictionaryCanon]
      exact dif_pos hbZ]
    exact AddEquiv.apply_symm_apply
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔)
      ((Work.AbsoluteKummer.mapH1 Φd.toAddMonoidHom hΦ)
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩))
  -- **Step 2**: its restriction to `⟨c⟩` vanishes, `b` being a coboundary there
  have hres : Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers c)
      (Work.SSGRoute.homCoind k Ω K 𝓔)
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) 𝓔
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0 := by
    rw [hcls]
    rw [resH1_mapH1 (Nsub := Subgroup.zpowers c) (θ := Φd.toAddMonoidHom) (hθ := hΦ)
      (hθ' := fun σ e => hΦ (σ : Ω ≃ₐ[k] Ω) e)
      (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)]
    rw [show (Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers c) E)
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) = 0 from by
      rw [Work.SSGRoute.PT.H2Fin.resH1_H1π, Work.AbsoluteKummer.H1π_eq_zero_iff]
      exact resZ1_mem_absB1_of_isCoboundaryOn (Subgroup.zpowers c) b hbZ hcob]
    rw [map_zero]
  -- the place, read as an infinite place
  have hle : SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
      ≤ (Subgroup.zpowers c).map (SSGRoute.res k K) :=
    le_of_eq (Work.SSGRoute.PT.decompK_linked k Ω K c hc2 hc1 φ hlink)
  have hne' : SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite
        (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) ≠ ⊥ := by
    rw [← hw]
    exact hne
  -- **Step 3**: the archimedean crux, in the two possible readings of the seam
  have hcrux : (SSGRoute.PTExt.extRes
        (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofInfinite
            (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))).subtype
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.unitsToLocalUnits k ↥K
          (NK.GlobalCFT.Place.ofInfinite
            (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))))
      (add_zero 1) = 0 := by
    rcases NumberField.InfinitePlace.embedding_mk_eq (φ.comp (algebraMap ↥K Ω)) with hcase | hcase
    · -- the seam is `φ` itself
      refine archCruxA_gen_linked (k := k) (Ω := Ω) (K := K)
        (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))) c hc2 φ ?_ hlink hle hne' 𝓔
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b) hres
      intro y
      show φ (algebraMap ↥K Ω y) = (NumberField.InfinitePlace.embedding
        (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) y
      rw [hcase]
      rfl
    · -- the seam is its complex conjugate
      refine archCruxA_gen_linked (k := k) (Ω := Ω) (K := K)
        (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))) c hc2
        (NumberField.ComplexEmbedding.conjugate φ) ?_ ?_ hle hne' 𝓔
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b) hres
      · intro y
        show (NumberField.ComplexEmbedding.conjugate φ) (algebraMap ↥K Ω y)
          = (NumberField.InfinitePlace.embedding
              (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) y
        rw [hcase]
        rfl
      · intro x
        have h1 : (NumberField.ComplexEmbedding.conjugate φ) (c x)
            = starRingEnd ℂ (φ (c x)) := rfl
        have h2 : (NumberField.ComplexEmbedding.conjugate φ) x
            = starRingEnd ℂ (φ x) := rfl
        rw [h1, h2, hlink x]
  -- **Step 4**: read the localisation as the restricted class composed with the local units
  rw [Work.SSGRoute.SSGStage.extLoc_extToIdeles_eq (k := k) (K := ↥K) w
    (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)]
  rw [hw]
  exact hcrux

end

end Work.SSGRoute.ArchDictionary
