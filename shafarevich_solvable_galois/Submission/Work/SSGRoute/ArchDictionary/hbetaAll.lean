import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.ArchDictionary.archDictTwoCore
import Submission.Work.SSGRoute.ArchDictionary.archDict_localZero_imp_coboundary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (β) for `archimedeanDictNonsplit`, from the narrow `p = 2` core

The target `Work.SSGRoute.ArchDictionary.archimedeanDictNonsplit` needs the hypothesis

* **(β)** `extLoc w (extToIdeles (globalDictionaryCanon … b)) = 0 → IsCoboundaryOn … b`

of `exists_square_of_components` for *every* prime `p` (the statement of that lemma takes it as a
hypothesis, even though only its `p = 2` branch uses it).  This file assembles (β) from

* the **narrow `p = 2` core** `Work.ArchDictionary.archDictTwoCore` — the arithmetic content (★) of
  `ArchDictionary/NOTE_localZero_imp_coboundary_strategy.md` §3: the vanishing of the localisation
  of the global class at the complex place forces its `E1c` class to restrict to `0` on `⟨c⟩`;
* the **proved assembly** `archDict_resH1_zpowers_eq_zero_imp_coboundary` (the formal inverse of
  the (α)-computation), and
* the **proved** odd case `archDict_localZero_imp_coboundary_odd` (where `Ac` vanishes),

so that the target depends on the `p = 2` arithmetic alone and not on the whole of the sibling
lemma `archDict_localZero_imp_coboundary`.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- **(β) at `p = 2`**, from the narrow arithmetic core and the (proved) assembly. -/
theorem archDict_localZero_imp_coboundary_two_own (p : ℕ) [Fact p.Prime] (hp : p = 2)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
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
    (hγ : SSGRoute.PTExt.extLoc (k := k) w
      (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hfin' : Finite ↥(Eprime p k Ω K T E) :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  haveI hMfinZ : Module.Finite ℤ ↑(Eprime p k Ω K T E) := Module.Finite.of_finite
  exact archDict_resH1_zpowers_eq_zero_imp_coboundary p ζ hζ hζK T hT E c hc2 b hb hl
    (Work.ArchDictionary.archDictTwoCore p hp k Ω K ζ hζ hζK T hT E c hc2 hc1 w φ hwinf hw
      hlink hne b hb hl hγ)

/-- **(β) for every prime `p`**: the `p = 2` case from the arithmetic core, the odd case for free. -/
theorem archDict_localZero_imp_coboundary_own (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
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
    (hγ : SSGRoute.PTExt.extLoc (k := k) w
      (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
  by_cases hp : p = 2
  · exact archDict_localZero_imp_coboundary_two_own p hp k Ω K ζ hζ hζK T hT E c hc2 hc1 w φ
      hwinf hw hlink hne b hb hl hγ
  · exact archDict_localZero_imp_coboundary_odd p hp k Ω K E c hc2 b hb

end

end Work.SSGRoute.ArchDictionary
