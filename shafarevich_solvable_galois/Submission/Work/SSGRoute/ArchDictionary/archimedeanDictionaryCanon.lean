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
import Submission.Work.SSGRoute.ArchDictionary.archPlaceDictBranches
import Submission.Work.SSGRoute.ArchDictionary.archPlaceDict_of_nonsplit_p2
import Submission.Work.SSGRoute.ArchDictionary.archimedeanDictNonsplit
import Submission.Work.SSGRoute.ArchDictionary.archimedeanDictSplitPlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean clause (4) of the local dictionary, at a fixed coefficient

Requested lemma: `Work.SSGRoute.ArchDictionary.archimedeanDictionaryCanon`, the archimedean clause
(4) of the local dictionary read off at a *single* coefficient module `E`.  It is dispatched on
`decompK w = ⊥` into the two **fixed-coefficient** case lemmas that were already on disk:

* `ArchDictionary.archimedeanDictSplitPlace` — the split (real) place `decompK w = ⊥`
  (`ArchDictionary/archimedeanDictSplitPlace.lean`), built from the lift·2 functional family
  `ArchSplit2.ell_bot_family` and its value on the canonical global class
  (`ArchSplit2.archSplit2_square_sign`), via `splitPlace_of_ell`;
* `ArchDictionary.archimedeanDictNonsplit` — the nonsplit (complex) place
  (`ArchDictionary/archimedeanDictNonsplit.lean`), built from the local dictionary
  `archLocDictionaryEquiv` (`Ext¹_{D_w}(E'|,K_wˣ) ≃+ Ac`) together with the two kernel inclusions
  (α) `archDict_coboundary_imp_localZero` and (β) `archDict_localZero_imp_coboundary_own`, via
  `exists_square_of_components`.

Both rest only on `propext`, `Classical.choice`, `Quot.sound` (measured), so this theorem rests on
none of the `E`-indexed `p = 2` seam machinery.

`ArchPlaceDict`, the `E`-indexed family *with its coefficient-naturality clause*, is strictly
stronger; it is what the leaf `E1aClean.localDictionary_natural_family_arch` consumes, and it is
stated (and case-split the same way) in the sibling module
`ArchDictionary/archPlaceDictHolds.lean`, which this module imports and so re-exports.  That
`E`-indexed half is the only part that still needs the coefficient-natural construction
(`ArchDictionary.archPlaceDict_of_nonsplit_p2`, lead design `_lead_design/archp2_1008`); the fixed
coefficient form below is independent of it.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

/-- **The `E`-indexed archimedean per-place dictionary** (the lead's restatement,
`_lead_design/ssg_natwit_0820.{md,lean}`).  Its conclusion `LeadNatWit.ArchPlaceDict` is the
`E`-indexed comparison square with its coefficient-naturality clause — verbatim the `hsq` input of
the proved `ArchNat.archimedeanDictUniformNat`, and the archimedean half of the leaf
`E1aClean.localDictionary_natural_family_arch`.

The case split is on `decompK w = ⊥`, a condition on `w` alone (so naturality — a statement about the
family indexed by `E` — is unaffected):

* `decompK w = ⊥` (real place): `ArchDictionary.archPlaceDict_of_split` (proved, clean);
* `decompK w ≠ ⊥`, `p ≠ 2`: `ArchDictionary.archPlaceDict_of_nonsplit_odd` (proved, clean — both
  sides are subsingletons since `2` is invertible);
* `decompK w ≠ ⊥`, `p = 2` (complex place): the coefficient-natural seam construction
  `ArchDictionary.archPlaceDict_of_nonsplit_p2`
  (`ArchDictionary/archPlaceDict_of_nonsplit_p2.lean`, lead design `_lead_design/archp2_1008`),
  `Φ = acH1Equiv ≫ cycTransfer ≫ mapH1(seamCoeffLoc) ≫ (NatH1.eOf)⁻¹` together with its comparison
  square.  This is the only part of the archimedean lane that needs the coefficient-natural
  construction.

The *fixed-coefficient* form `archimedeanDictionaryCanon` below does **not** need that construction:
it is proved directly from the two fixed-coefficient case lemmas `archimedeanDictSplitPlace`
(`ArchDictionary/archimedeanDictSplitPlace.lean`) and `archimedeanDictNonsplit`
(`ArchDictionary/archimedeanDictNonsplit.lean`), which were already on disk and rest only on
`propext`, `Classical.choice`, `Quot.sound`. -/
theorem archPlaceDict_holds (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ φ : Ω →+* ℂ,
      (∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) → ∀ w : NK.GlobalCFT.Place ↥K,
      w = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω))) →
      Work.SSGRoute.LeadNatWit.ArchPlaceDict p k Ω K ζ hζ hζK T hT c w := by
  intro c hc2 hc1 φ hlink w hw
  by_cases hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥
  · exact archPlaceDict_of_split (k := k) (Ω := Ω) (K := K) p ζ hζ hζK T hT c hc2 hc1 φ hlink
      w hw hbot
  · by_cases hp2 : p = 2
    · subst hp2
      exact archPlaceDict_of_nonsplit_p2 (k := k) (Ω := Ω) (K := K) ζ hζ hζK T hT c hc2 hc1 φ
        hlink w hw hbot
    · exact archPlaceDict_of_nonsplit_odd (k := k) (Ω := Ω) (K := K) p hp2 ζ hζ hζK T hT c hc2
        hc1 φ hlink w hw hbot

/-- **The fixed-coefficient form of the archimedean dictionary** (the exact original request).

This is the archimedean clause (4) of the local dictionary read off at a single coefficient module
`E`.  It is dispatched on `decompK w = ⊥` to the two *fixed-coefficient* case lemmas:

* `ArchDictionary.archimedeanDictSplitPlace` — the split (real) place `decompK w = ⊥`
  (`ArchDictionary/archimedeanDictSplitPlace.lean`), built from the lift·2 functional family
  `ArchSplit2.ell_bot_family` and its value on the canonical global class
  (`ArchSplit2.archSplit2_square_sign`);
* `ArchDictionary.archimedeanDictNonsplit` — the nonsplit (complex) place, built from the local
  dictionary `archLocDictionaryEquiv` (`Ext¹_{D_w}(E'|,K_wˣ) ≃+ Ac`) together with the two kernel
  inclusions (α) `archDict_coboundary_imp_localZero` and (β)
  `archDict_localZero_imp_coboundary_own`, via `exists_square_of_components`.

Both rest only on `propext`, `Classical.choice` and `Quot.sound` (measured), so this theorem — the
assignment — rests on *none* of the
`E`-indexed p = 2 machinery of `archPlaceDict_of_nonsplit_p2` above.  (`ArchPlaceDict`, the
`E`-indexed family with its naturality clause, is strictly stronger: it is what the leaf
`E1aClean.localDictionary_natural_family_arch` consumes, and it does need the coefficient-natural
construction.)

It is the shape in which `ArchDictionary.archFamilyClause` consumes the dictionary. -/
theorem archimedeanDictionaryCanon (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
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
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) :
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
  by_cases hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥
  · exact archimedeanDictSplitPlace p k Ω K ζ hζ hζK T hT E c hc2 hc1 w φ hwinf hw hlink hbot
  · exact archimedeanDictNonsplit p k Ω K ζ hζ hζK T hT E c hc2 hc1 w φ hwinf hw hlink hbot

end Work.SSGRoute.ArchDictionary
