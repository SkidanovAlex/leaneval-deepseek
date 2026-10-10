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
import Submission.Work.ArchDictionary.archAcEquivH1loc
import Submission.Work.SSGRoute.ArchDictionary.AcOdd
import Submission.Work.SSGRoute.ArchDictionary.ArchLinAlg
import Submission.Work.SSGRoute.ArchDictionary.assemblyOfSquare
import Submission.Work.SSGRoute.PT.pt_counting_assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The comparison square from its three components

The target `archimedeanDictNonsplit` follows from the comparison square
(`archimedeanDictNonsplit_of_square`), and the square follows from

* **(L1)** `L ≅ Ac` (the archimedean local dictionary, `ArchDictionary.archLocDictionaryEquiv`);
* **(α)** `ker ρ̄ ⊆ ker γ̄` (proved in `ArchDictionary.archDictCoboundaryImpLocalZero`);
* **(β)** `ker γ̄ ⊆ ker ρ̄` (`ArchDictionary.archDict_localZero_imp_coboundary`),

where `ρ̄ b = [b|⟨c⟩]` and `γ̄ b = extLoc w (extToIdeles (globalDictionaryCanon … b))`.

* For **odd `p`** the statement is immediate: `Ac` is trivial (`Ac_subsingleton_of_odd`), hence so
  is `L`, and any additive equivalence does.
* In general the argument is **uniform in `p`**: transport both `ρ̄` and `L ≅ Ac` into the concrete
  local group `H¹(⟨c⟩,E) = H1loc p k Ω K E (Subgroup.zpowers c)` (finite dimensional by
  `PT.pt_counting_assembly`), where the two maps have the same kernel by (α) and (β) and hence
  differ by an automorphism (`ArchLinAlg.exists_addEquiv_of_ker_eq`).  The identification
  `Ac ≅ H1loc p k Ω K E (Subgroup.zpowers c)` is `archAcEquivH1loc`.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-- Every element of a `ℤ/pℤ`-module is killed by `p`. -/
theorem nsmul_prime_eq_zero (p : ℕ) {E : Type} [AddCommGroup E] [Module (ZMod p) E] (e : E) :
    p • e = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) p e, ZMod.natCast_self, zero_smul]

/-- **The general (uniform in `p`) construction of the comparison square.**

Given the local dictionary isomorphism `hL1 : L ≃+ Ac`, the two inclusions of kernels (α) and (β)
*and* the identification `eA : Ac ≃+ H¹(⟨c⟩,E) = H1loc …` compatible with the class maps, the
square holds.

The `p = 2` branch of `exists_square_of_components` is this statement with `eA` produced by
`archAcEquivH1loc`; for odd `p` the statement is *stronger* than needed and the trivial argument
avoids (β). -/
theorem exists_square_of_components_general (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (w : NK.GlobalCFT.Place ↥K)
    (hL1 : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1 ≃+ Ac (K := K) (E := E) c)
    (halpha : ∀ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      SSGRoute.PTExt.extLoc (k := k) w
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0)
    (hbeta : ∀ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.PTExt.extLoc (k := k) w
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0 →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (eA : Ac (K := K) (E := E) c ≃+ H1loc p k Ω K E (Subgroup.zpowers c))
    (heA : ∀ (b : (Ω ≃ₐ[k] Ω) → E) (hb : b ∈ Zc (K := K) (E := E) c),
      eA (Acπ (K := K) (E := E) c ⟨b, hb⟩) = toClass p k Ω K E (Subgroup.zpowers c) b) :
    ∃ Φ : Ac (K := K) (E := E) c ≃+ CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      ∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        Φ (AcOfFun (K := K) (E := E) c b)
          = SSGRoute.PTExt.extLoc (k := k) w
              (SSGRoute.PTExt.extToIdeles (k := k)
                (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) := by
  classical
  -- the domain of the two maps: the global locally constant cocycles
  let H := ↥(lcCocycles p k Ω K E (⊤ : Subgroup (Ω ≃ₐ[k] Ω)))
  have htor : ∀ e : E, p • e = 0 := nsmul_prime_eq_zero p
  have hHexp : ∀ x : H, p • x = 0 := by
    intro x
    refine Subtype.ext (funext fun g => htor ((x : (Ω ≃ₐ[k] Ω) → E) g))
  haveI hfin : Finite (H1loc p k Ω K E (Subgroup.zpowers c)) :=
    Work.SSGRoute.PT.finite_H1loc_zpowers p k Ω K E c hc2
  haveI hfinmod : Module.Finite (ZMod p) (H1loc p k Ω K E (Subgroup.zpowers c)) :=
    Module.Finite.of_finite
  -- every global locally constant cocycle is a locally constant cocycle on `⟨c⟩`
  have hmem : ∀ b : H,
      ((b : (Ω ≃ₐ[k] Ω) → E) ∈ lcCocycles p k Ω K E (Subgroup.zpowers c)) := by
    intro b
    refine (Work.SSGRoute.mem_lcCocycles p k Ω K E (Subgroup.zpowers c)
      (b : (Ω ≃ₐ[k] Ω) → E)).mpr
      ⟨fun g _ h _ => (Work.SSGRoute.mem_lcCocycles p k Ω K E ⊤
          (b : (Ω ≃ₐ[k] Ω) → E)).mp b.2 |>.1 g trivial h trivial,
        Work.SSGRoute.H1Pair.isLocConstOn_zpowers_of_sq_eq_one c hc2 _⟩
  -- the restriction of a global cocycle to `⟨c⟩`
  let ρmap : H →+ H1loc p k Ω K E (Subgroup.zpowers c) :=
    { toFun := fun b => toClass p k Ω K E (Subgroup.zpowers c) (b : (Ω ≃ₐ[k] Ω) → E)
      map_zero' := by
        have hz : ((0 : H) : (Ω ≃ₐ[k] Ω) → E) ∈ lcCocycles p k Ω K E (Subgroup.zpowers c) := by
          simpa using zero_mem (lcCocycles p k Ω K E (Subgroup.zpowers c))
        rw [Work.SSGRoute.toClass, dif_pos hz]
        simp
      map_add' := fun b b' => by
        rw [Submodule.coe_add]
        exact Work.SSGRoute.toClass_add p k Ω K E (Subgroup.zpowers c) (hmem b) (hmem b') }
  -- the localisation of the canonical global class
  let γmap : H →+ CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime p k Ω K T E))
      (SSGRoute.PTExt.localUnitsK (k := k) w) 1 :=
    { toFun := fun b => SSGRoute.PTExt.extLoc (k := k) w
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E
            (b : (Ω ≃ₐ[k] Ω) → E)))
      map_zero' := by
        have h0mem : ((0 : H) : (Ω ≃ₐ[k] Ω) → E) ∈ lcCocycles p k Ω K E ⊤ := by
          simpa using zero_mem (lcCocycles p k Ω K E (⊤ : Subgroup (Ω ≃ₐ[k] Ω)))
        have h0' := (Work.SSGRoute.mem_lcCocycles p k Ω K E ⊤
          ((0 : H) : (Ω ≃ₐ[k] Ω) → E)).mp h0mem
        have hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤
            ((0 : H) : (Ω ≃ₐ[k] Ω) → E) := ⟨0, fun g _ => by simp⟩
        have hz : Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E
            ((0 : H) : (Ω ≃ₐ[k] Ω) → E) = 0 :=
          ((Work.SSGRoute.E1aClean.globalDictionaryCanon_spec p k Ω K ζ hζ hζK T hT E).2.1
            ((0 : H) : (Ω ≃ₐ[k] Ω) → E) h0'.1 h0'.2).mpr hcob
        rw [hz, SSGRoute.PTExt.extToIdeles_zero (k := k) (K := ↥K),
          SSGRoute.PTExt.extLoc_zero (k := k) (K := ↥K) w]
      map_add' := fun b b' => by
        have hb := (Work.SSGRoute.mem_lcCocycles p k Ω K E ⊤
          (b : (Ω ≃ₐ[k] Ω) → E)).mp b.2
        have hb' := (Work.SSGRoute.mem_lcCocycles p k Ω K E ⊤
          (b' : (Ω ≃ₐ[k] Ω) → E)).mp b'.2
        have hgd := (Work.SSGRoute.E1aClean.globalDictionaryCanon_spec p k Ω K ζ hζ hζK T hT E).1
          (b : (Ω ≃ₐ[k] Ω) → E) (b' : (Ω ≃ₐ[k] Ω) → E) hb.1 hb.2 hb'.1 hb'.2
        have hcoe : ((b + b' : H) : (Ω ≃ₐ[k] Ω) → E)
            = (b : (Ω ≃ₐ[k] Ω) → E) + (b' : (Ω ≃ₐ[k] Ω) → E) := rfl
        change SSGRoute.PTExt.extLoc (k := k) w
            (SSGRoute.PTExt.extToIdeles (k := k)
              (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E (↑(b + b'))))
          = SSGRoute.PTExt.extLoc (k := k) w
              (SSGRoute.PTExt.extToIdeles (k := k)
                (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E ↑b))
            + SSGRoute.PTExt.extLoc (k := k) w
              (SSGRoute.PTExt.extToIdeles (k := k)
                (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E ↑b'))
        rw [hcoe, hgd, SSGRoute.PTExt.extToIdeles_add (k := k) (K := ↥K),
          SSGRoute.PTExt.extLoc_add (k := k) (K := ↥K)] }
  -- the kernels agree, by (α) and (β)
  have hker : ∀ b : H, ρmap b = 0 ↔
      ((hL1.trans eA).toAddMonoidHom.comp γmap) b = 0 := by
    intro b
    have hb := (Work.SSGRoute.mem_lcCocycles p k Ω K E ⊤
      (b : (Ω ≃ₐ[k] Ω) → E)).mp b.2
    have hcomp : ((hL1.trans eA).toAddMonoidHom.comp γmap) b
        = (hL1.trans eA) (SSGRoute.PTExt.extLoc (k := k) w
            (SSGRoute.PTExt.extToIdeles (k := k)
              (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E
                (b : (Ω ≃ₐ[k] Ω) → E)))) := rfl
    have hρ : ρmap b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K)
        (Subgroup.zpowers c) (b : (Ω ≃ₐ[k] Ω) → E) := by
      show toClass p k Ω K E (Subgroup.zpowers c) (b : (Ω ≃ₐ[k] Ω) → E) = 0 ↔ _
      rw [Work.SSGRoute.toClass_eq_zero_iff p k Ω K E (Subgroup.zpowers c) (hmem b)]
      exact Work.SSGRoute.mem_coboundaries p k Ω K E (Subgroup.zpowers c) _
    rw [hρ, hcomp, (hL1.trans eA).map_eq_zero_iff]
    exact ⟨halpha _ hb.1 hb.2, hbeta _ hb.1 hb.2⟩
  obtain ⟨Ψ, hΨ⟩ := exists_addEquiv_of_ker_eq p hHexp ρmap
    ((hL1.trans eA).toAddMonoidHom.comp γmap) hker
  refine ⟨eA.trans (Ψ.trans (hL1.trans eA).symm), ?_⟩
  intro b hbG hlG
  have hbH : b ∈ lcCocycles p k Ω K E ⊤ :=
    (Work.SSGRoute.mem_lcCocycles p k Ω K E ⊤ b).mpr ⟨hbG, hlG⟩
  have hbZc : b ∈ Zc (K := K) (E := E) c := mem_Zc_of_global (K := K) (E := E) hbG
  rw [AcOfFun_eq (K := K) (E := E) c b hbZc]
  change (hL1.trans eA).symm (Ψ (eA (Acπ (K := K) (E := E) c ⟨b, hbZc⟩)))
    = SSGRoute.PTExt.extLoc (k := k) w
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
  rw [heA b hbZc]
  rw [show toClass p k Ω K E (Subgroup.zpowers c) b = ρmap ⟨b, hbH⟩ from rfl, hΨ ⟨b, hbH⟩]
  change (hL1.trans eA).symm ((hL1.trans eA) (γmap ⟨b, hbH⟩))
    = SSGRoute.PTExt.extLoc (k := k) w
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- **The comparison square from the three components.** -/
theorem exists_square_of_components (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
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
    (hL1 : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1 ≃+ Ac (K := K) (E := E) c)
    (halpha : ∀ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      SSGRoute.PTExt.extLoc (k := k) w
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0)
    (hbeta : ∀ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.PTExt.extLoc (k := k) w
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0 →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    ∃ Φ : Ac (K := K) (E := E) c ≃+ CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      ∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        Φ (AcOfFun (K := K) (E := E) c b)
          = SSGRoute.PTExt.extLoc (k := k) w
              (SSGRoute.PTExt.extToIdeles (k := k)
                (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) := by
  classical
  by_cases hp2 : p = 2
  · -- `p = 2`: the general argument, with `Ac ≅ H¹(⟨c⟩,E)` supplied by `archAcEquivH1loc`
    obtain ⟨eA, heA⟩ := Work.ArchDictionary.archAcEquivH1loc p k Ω K E c hc2
    exact exists_square_of_components_general p k Ω K ζ hζ hζK T hT E c hc2 w hL1 halpha hbeta
      eA heA
  · -- odd `p`: `Ac` is trivial, hence so is `L`
    haveI hAc : Subsingleton (Ac (K := K) (E := E) c) :=
      Ac_subsingleton_of_odd (K := K) (p := p) (E := E) hp2 c hc2
    haveI hL : Subsingleton (CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1) :=
      ⟨fun x y => hL1.injective (Subsingleton.elim (hL1 x) (hL1 y))⟩
    exact ⟨hL1.symm, fun b hb hl => Subsingleton.elim _ _⟩

end

end Work.SSGRoute.ArchDictionary
