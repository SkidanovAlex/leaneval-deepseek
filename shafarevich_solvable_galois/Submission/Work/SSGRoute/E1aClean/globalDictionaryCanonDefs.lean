import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1aClean.LocalExtensionAux
import Submission.Work.SSGRoute.E1aClean.coeffIsoNatural_generic
import Submission.Work.SSGRoute.E1aClean.decompDatumFacts
import Submission.Work.SSGRoute.E1aClean.h1AddEquivNat
import Submission.Work.SSGRoute.E1aClean.localDictFromFamily
import Submission.Work.SSGRoute.E1aClean.unitsQuotient_pow_bijective_fixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! ## The named (canonical) global dictionary — definitions module

`Work.SSGRoute.E1aClean.globalDictionary` of `ext_h1_localGlobal_dictionary.lean` is built on
`Classical.choice (h1_equiv_of_equiv Φd hΦd)`, an *opaque* choice of the coefficient transport; the
comparison square with the local dictionary needs the transport to be the canonical *named* map
`H1Equiv.h1AddEquiv`, so that both sides of the square are given by the same free-cover
construction.  This module re-does the global dictionary with the named transport.

It was split out of `E1aClean/localDictionary_natural_family.lean` (lead ruling
`_lead_design/ssg_natwit_0820.md`, STEP 0) so that the per-place-witness definitions the lead
installs on top of it do not import the leaf (which would be an import cycle).  The leaf imports
this module, so every consumer of the leaf still sees these names. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

section GlobalCanon

/-- **The canonical global dictionary equivalence** `H¹(G_k,E) ≃+ Ext¹_Γ(E',Kˣ)`, with the
coefficient transport realised by the named map `H1Equiv.h1AddEquiv` (so that it is the *same*
construction as the local one). -/
noncomputable def globalDictEquivCanon (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) ≃+
      CategoryTheory.Abelian.Ext
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
        (SSGRoute.PTExt.unitsK k K) 1 := by
  classical
  haveI : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  let 𝓔 : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
  haveI : Finite (𝓔 : Type) := by
    change Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
    exact Work.SSGRoute.PT.finite_dualMod_tensor p E T
  haveI : Module.Finite ℤ (𝓔 : Type) := Module.Finite.of_finite
  let Φd := Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E
  have hΦ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.toAddMonoidHom :=
    fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e
  have hΨ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.symm.toAddMonoidHom :=
    fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n
  exact (Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦ hΨ).trans
    (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔).symm

/-- **The canonical global dictionary**, on all functions (zero off the cocycles). -/
noncomputable def globalDictionaryCanon (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ((Ω ≃ₐ[k] Ω) → E) →
      CategoryTheory.Abelian.Ext
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
        (SSGRoute.PTExt.unitsK k K) 1 := by
  classical
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  exact fun b =>
    if h : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E then
      globalDictEquivCanon p k Ω K ζ hζ hζK T hT E
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, h⟩)
    else 0

/-- **The three clauses of the canonical global dictionary** (additive on cocycles, kernel the
coboundaries, onto). -/
theorem globalDictionaryCanon_spec (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
        globalDictionaryCanon p k Ω K ζ hζ hζK T hT E (b + b')
          = globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b
            + globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        (globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b = 0 ↔
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b)) ∧
      (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
        SSGRoute.IsLocConstOn ⊤ b ∧ globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b = y) := by
  classical
  haveI : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  refine ⟨?_, ?_, ?_⟩
  · intro b b' hb hl hb' hl'
    have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hl
    have hbZ' : b' ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb' hl'
    have hbbZ : b + b' ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E).add_mem hbZ hbZ'
    dsimp only [globalDictionaryCanon]
    rw [dif_pos hbbZ, dif_pos hbZ, dif_pos hbZ']
    have hπ : Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b + b', hbbZ⟩
        = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩
          + Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b', hbZ'⟩ := by
      rw [show (⟨b + b', hbbZ⟩ : Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E)
          = ⟨b, hbZ⟩ + ⟨b', hbZ'⟩ from Subtype.ext rfl, map_add]
    rw [hπ, map_add]
  · intro b hb hl
    have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hl
    dsimp only [globalDictionaryCanon]
    rw [dif_pos hbZ]
    rw [(globalDictEquivCanon p k Ω K ζ hζ hζK T hT E).map_eq_zero_iff]
    rw [Work.AbsoluteKummer.H1π_eq_zero_iff]
    rw [mem_absB1_iff_exists]
    exact (isCoboundaryOn_top_iff_class_eq_zero (SSGRoute.res k K) b).symm
  · intro y
    obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) E).comap
        (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E).subtype)
      ((globalDictEquivCanon p k Ω K ζ hζ hζK T hT E).symm y)
    refine ⟨c.1, (isCocycleOn_iff_mem_Z1 (SSGRoute.res k K) c.1).mpr c.2.1,
      top_isLocConstOn_of_isLocallyConstant c.2.2, ?_⟩
    dsimp only [globalDictionaryCanon]
    rw [dif_pos c.2]
    rw [show (⟨c.1, c.2⟩ : Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E) = c from Subtype.ext rfl]
    rw [show Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E c
        = (globalDictEquivCanon p k Ω K ζ hζ hζK T hT E).symm y from hc]
    exact AddEquiv.apply_symm_apply _ y

end GlobalCanon

/-! ## Naturality of the `H¹`-coefficient transport

A general fact used in the comparison of the global and local dictionaries: the `H¹`-transport
`H1Equiv.h1AddEquiv` (the *named* map `mapH1` of an equivariant additive equivalence) is natural. -/

section H1TransportNat

open Work.AbsoluteKummer

theorem h1AddEquiv_symm_eq_mapH1 {G : Type} [Group G] [TopologicalSpace G]
    {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction G M] [DistribMulAction G N] (Φ : M ≃+ N)
    (hΦ : Work.GroupCohomology.IsEquivariant G Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant G Φ.symm.toAddMonoidHom) :
    (Work.SSGRoute.H1Equiv.h1AddEquiv Φ hΦ hΨ).symm
      = Work.AbsoluteKummer.mapH1 Φ.symm.toAddMonoidHom hΨ := by
  ext z
  rfl

end H1TransportNat

end Work.SSGRoute.E1aClean
