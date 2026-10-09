import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.DualMod.Main
-- import cut: this file only uses `E1aClean.globalDictionaryCanon`, which lives leaf-free in
-- `globalDictionaryCanonDefs`; the leaf import would put `E1aClean.localDictionary_natural_family`
-- into `cone(ArchDictionary.archimedeanDictionaryCanon)`, which the leaf's own closure imports.
import Submission.Work.SSGRoute.E1aClean.globalDictionaryCanonDefs
import Submission.Work.SSGRoute.ArchDictionary.assemblyOfSquare
import Submission.Work.SSGRoute.ArchDictionary.squareOfComponents
import Submission.Work.SSGRoute.ArchDictionary.archLocDictionaryEquiv
import Submission.Work.SSGRoute.ArchDictionary.archDict_coboundary_imp_localZero
import Submission.Work.SSGRoute.ArchDictionary.archDict_localZero_imp_coboundary
import Submission.Work.SSGRoute.ArchDictionary.hbetaAll
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

theorem archimedeanDictNonsplit (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
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
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    ∃ βc : ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        βc (b + b') = βc b + βc b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (βc b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) ∧
      (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc b = y) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        SSGRoute.PTExt.extLoc (k := k) w
          (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = βc b) := by
  classical
  obtain ⟨hL1⟩ := archLocDictionaryEquiv p k Ω K ζ hζ hζK T hT E c hc2 hc1 w φ hwinf hw hlink hne
  exact archimedeanDictNonsplit_of_square p k Ω K ζ hζ hζK T hT E c hc2 hc1 w φ hwinf hw hlink hne
    (exists_square_of_components p k Ω K ζ hζ hζK T hT E c hc2 hc1 w φ hwinf hw hlink hne hL1
      (archDict_coboundary_imp_localZero p k Ω K ζ hζ hζK T hT E c hc2 hc1 w φ hwinf hw hlink hne)
      (fun b hb hl hγ => archDict_localZero_imp_coboundary_own p k Ω K ζ hζ hζK T hT E c hc2 hc1
        w φ hwinf hw hlink hne b hb hl hγ))

end Work.SSGRoute.ArchDictionary
