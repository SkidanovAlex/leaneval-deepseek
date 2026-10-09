import Mathlib
import Submission.Work.SSGRoute.PT.e1a_can_chain
import Submission.Work.SSGRoute.PT.e1a_sha2_mem_deltaRange_gen
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.PT.homCoindFree_coind_iso_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The arithmetic crux for the canonical chain `e1aChainC`

`Work.SSGRoute.PT.e1aChainC` is the canonical, choice-free chain
`Ext²_G(E',Kˣ) →+ H²(Γ,E)` (`E' = DualMod p (E ⊗ T)`) assembled in `PT/e1a_can_chain.lean` from the
canonical syzygy shift, the explicit `E1c` dictionary and the connecting map of the dualised
canonical resolution, followed by the canonical coefficient identification.  This file proves the
membership clause needed to invert it on the classes of locally trivial cocycles:

> every `H2π c ∈ H²(Γ,E)` with `c ∈ Z2loc` lies in the range of `e1aChainC`.

The proof is the Shapiro computation `e1a_sha2_mem_deltaRange_gen` with the *canonical* cover
`freeCover N` of `N = E'` instead of a `Fin n`-indexed one: the crux is restated for an arbitrary
finite index type (`e1a_sha2_mem_deltaRange_gen_iota`), which is exactly what the canonical cover
`freeCover N : Rep.free Coeff G N.V ⟶ N` needs.  The generalised Shapiro identification for an
arbitrary index type is `homCoindFree_coind_iso_gen`.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/- The canonical syzygy has a finite underlying `ℤ`-module (the canonical presentation is the
`@[reducible] freeCoverSES` one). -/
attribute [local instance] Work.SSGRoute.freeCoverSES_finite

/-! ## The Shapiro computation for an arbitrary finite free cover index type -/

/-- **The arithmetic crux of E1a, for an arbitrary finite index type `ι`.**

This is `Work.SSGRoute.PT.e1a_sha2_mem_deltaRange_gen` with the `Fin n`-indexed free coefficient
`Work.SSGRoute.PT.homCoindFree k Ω K n` replaced by `Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι`
(`Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)`), which is what the canonical cover `freeCover N` of a module `N`
requires (`ι = N.V`).  The proof is the same Shapiro computation: `c` is a coboundary on the open
subgroup `G_K`, and the kernel half of Shapiro's lemma (`shapiro_kernel_transfer`, using the
`Gal(Ω/k)`-equivariant identification `homCoindFree_coind_iso_gen`) exhibits a primitive of the
transported cocycle on all of `G_k`, i.e. its class vanishes. -/
theorem e1a_sha2_mem_deltaRange_gen_iota (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (ι : Type) [Finite ι]
    (pic : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι ⟶
      SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (hf : Function.Surjective (Rep.Hom.hom pic))
    (S : Work.AbsoluteKummer.ShortExactSeq (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι)
      (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel pic)))
    (hS : S.iota = Work.SSGRoute.precompAddHom (Rep.Hom.hom pic).toAddMonoidHom)
    (δ : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel pic)) →+
      Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))))
    (hδ : δ.range = (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker)
    (Ψ : E ≃+ Work.SSGRoute.homCoind k Ω K (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
    (hΨ : ∀ (σ : Ω ≃ₐ[k] Ω) (e : E),
      Ψ ((SSGRoute.res k K σ) • e) = σ • Ψ e) :
    ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
      (hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
        @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
          (DistribMulAction.compHom E (SSGRoute.res k K))),
      c ∈ Work.SSGRoute.Z2loc p k Ω K E →
      ∃ z : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel pic)),
        δ z = e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E Ψ hΨ
          (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩) := by
  classical
  -- the action of `G_k` on the coefficients
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  intro c hZ hc
  -- ### the composite coefficient map
  have hΨ' : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Ψ.toAddMonoidHom :=
    fun σ e => hΨ σ e
  let Φ : E →+ Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι := S.iota.comp Ψ.toAddMonoidHom
  have hΦ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φ :=
    S.iota_equivariant.comp hΨ
  have hΦexp : ∀ (σ : Ω ≃ₐ[k] Ω) (e : E),
      Φ ((SSGRoute.res k K σ) • e) = S.iota (σ • Ψ e) := by
    intro σ e
    exact congrArg S.iota (hΨ' σ e)
  -- ### the cocycle, transported into the free (coinduced) coefficient
  let cZ : Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E := ⟨fun q => c q.1 q.2, hZ⟩
  let zZ : Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) :=
    Work.AbsoluteKummer.mapZ2 Φ hΦ cZ
  have hzZval : ∀ (σ τ : Ω ≃ₐ[k] Ω),
      (zZ : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) →
        Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) (σ, τ) = Φ (c σ τ) := by
    intro σ τ
    dsimp only [zZ, cZ]
    rw [Work.AbsoluteKummer.mapZ2_apply]
  -- ### the primitive of `c` on `G_K`, and the primitive of its transport
  obtain ⟨b₀, hb₀loc, hb₀eq⟩ :=
    Work.SSGRoute.sha2_restrict_vanish p k Ω K ζ hζ hζK E c hc
  let B' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι := fun σ => Φ (b₀ σ)
  -- ### the Shapiro isomorphism (general index type)
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨Zc, hZc⟩ : ∃ Zc : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι ≃+
      Coind (Ω ≃ₐ[k] Ω) (K.fixingSubgroup) (ι → Additive Ωˣ),
      Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Zc.toAddMonoidHom :=
    homCoindFree_coind_iso_gen k Ω K ι
  let b : K.fixingSubgroup → (ι → Additive Ωˣ) :=
    fun u => (Zc (B' (u : Ω ≃ₐ[k] Ω))) 1
  have hUopen : IsOpen (K.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen K
  haveI hFI : (K.fixingSubgroup).FiniteIndex := by
    have hker : (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) = (SSGRoute.res k K).ker :=
      (IntermediateField.restrictNormalHom_ker K).symm
    have hres : (SSGRoute.res k K).ker.FiniteIndex := by
      have hsurj : Function.Surjective (SSGRoute.res k K) :=
        AlgEquiv.restrictNormalHom_surjective Ω
      haveI : Fintype (K ≃ₐ[k] K) := AlgEquiv.fintype k ↥K
      haveI : Fintype ((Ω ≃ₐ[k] Ω) ⧸ (SSGRoute.res k K).ker) :=
        Fintype.ofEquiv (K ≃ₐ[k] K)
          (QuotientGroup.quotientKerEquivOfSurjective (SSGRoute.res k K) hsurj).toEquiv.symm
      exact Subgroup.finiteIndex_of_finite_quotient
    rwa [hker]
  have hbloc : b ∈ Work.AbsoluteKummer.C1c (K.fixingSubgroup) (ι → Additive Ωˣ) := by
    refine (Work.AbsoluteKummer.mem_C1c_iff b).mpr ?_
    have h1 : Work.AbsoluteKummer.IsLocallyConstant
        (fun u : K.fixingSubgroup => B' (u : Ω ≃ₐ[k] Ω)) :=
      isLocallyConstant_subtype_of_isLocConstOn K.fixingSubgroup
        (isLocConstOn_push hb₀loc Φ)
    exact h1.map (fun w => (Zc w) 1)
  have hbeq : Work.GroupCohomology.d1 (K.fixingSubgroup) (ι → Additive Ωˣ) b =
      fun p : K.fixingSubgroup × K.fixingSubgroup =>
        (Zc ((zZ : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) →
          Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) (p.1, p.2))) 1 := by
    funext p
    obtain ⟨u, v⟩ := p
    show u • b v - b (u * v) + b u =
      (Zc ((zZ : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) →
        Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) (u, v))) 1
    rw [hzZval (u : Ω ≃ₐ[k] Ω) (v : Ω ≃ₐ[k] Ω)]
    rw [hb₀eq (u : Ω ≃ₐ[k] Ω) u.2 (v : Ω ≃ₐ[k] Ω) v.2, map_add, map_sub,
      hΦexp (u : Ω ≃ₐ[k] Ω) (b₀ (v : Ω ≃ₐ[k] Ω)),
      S.iota_equivariant (u : Ω ≃ₐ[k] Ω) (Ψ (b₀ (v : Ω ≃ₐ[k] Ω)))]
    rw [show b v = (Zc (B' (v : Ω ≃ₐ[k] Ω))) 1 from rfl,
      show b (u * v) = (Zc (B' (((u * v : K.fixingSubgroup) : Ω ≃ₐ[k] Ω)))) 1 from rfl,
      show b u = (Zc (B' (u : Ω ≃ₐ[k] Ω))) 1 from rfl]
    rw [← coind_eval_smul K.fixingSubgroup Zc hZc u (B' (v : Ω ≃ₐ[k] Ω))]
    rw [map_add, map_sub]
    rfl
  -- ### the Shapiro kernel half
  have hzB : (zZ : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) →
      Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) ∈
      Work.AbsoluteKummer.B2 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) :=
    shapiro_kernel_transfer K.fixingSubgroup hUopen Zc hZc
      (zZ : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) → Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι)
      zZ.2 ⟨b, hbloc, hbeq⟩
  -- ### the cohomological chain
  have hchain : Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant
      (e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E Ψ hΨ
        (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ)) =
      Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) zZ := by
    calc Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant
          (e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E Ψ hΨ
            (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ))
        = Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant
            (Work.AbsoluteKummer.mapH2 Ψ.toAddMonoidHom hΨ
              (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ)) := rfl
      _ = Work.AbsoluteKummer.mapH2 (S.iota.comp Ψ.toAddMonoidHom)
            (S.iota_equivariant.comp hΨ)
            (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ) :=
          (Work.AbsoluteKummer.mapH2_comp_H2π Ψ.toAddMonoidHom S.iota hΨ
            S.iota_equivariant cZ).symm
      _ = Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) zZ :=
          Work.AbsoluteKummer.mapH2_H2π (S.iota.comp Ψ.toAddMonoidHom)
            (S.iota_equivariant.comp hΨ) cZ
  have hmem : Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant
      (e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E Ψ hΨ
        (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ)) = 0 := by
    rw [hchain, Work.AbsoluteKummer.H2π_eq_zero_iff]
    exact hzB
  have hmem' : e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E Ψ hΨ
      (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ) ∈ δ.range := by
    rw [hδ, AddMonoidHom.mem_ker]
    exact hmem
  obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.mpr hmem'
  exact ⟨z, hz⟩

/-! ## The coefficient identification is inverse to the canonical one on `H²` -/

/-- `e1aCoeffH2` (the `H²`-transport of the inverse of the canonical coefficient identification
`e1aCoeffNat`) is a left inverse of `e1aCoeffMapOf e1aCoeffNat`: the composite is
`mapH2 (e1aCoeffNat.symm ∘ e1aCoeffNat) = mapH2 id`, computed on classes of cocycles. -/
theorem e1aCoeffH2_e1aCoeffMapOf_e1aCoeffNat (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (x : @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))) :
    Work.SSGRoute.ExtChain.e1aCoeffH2 p k Ω K ζ hζ hζK T hT E
      (e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E
        (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E)
        (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e)
        x) = x := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  obtain ⟨c', hc'⟩ := Work.SSGRoute.ExtChain.h2π_surjective_aux (G := Ω ≃ₐ[k] Ω) (M := E) x
  rw [← hc']
  rw [show e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E
        (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E)
        (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e)
        (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E c') =
      Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (Work.AbsoluteKummer.mapZ2
          (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).toAddMonoidHom
          (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e)
          c')
      from Work.AbsoluteKummer.mapH2_H2π _ _ _]
  rw [show Work.SSGRoute.ExtChain.e1aCoeffH2 p k Ω K ζ hζ hζK T hT E
        (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.homCoind k Ω K (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (Work.AbsoluteKummer.mapZ2
            (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).toAddMonoidHom
            (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e)
            c')) =
      Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E
        (Work.AbsoluteKummer.mapZ2
          (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm.toAddMonoidHom
          (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant
            p k Ω K ζ hζ hζK T hT E σ n)
          (Work.AbsoluteKummer.mapZ2
            (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).toAddMonoidHom
            (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e)
            c'))
      from Work.AbsoluteKummer.mapH2_H2π _ _ _]
  congr 1
  apply Subtype.ext
  funext q
  exact (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm_apply_apply
    ((c' : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) → E) q)

/-! ## The membership clause for the canonical chain -/

/-- **The class of a locally trivial cocycle lies in the range of the canonical chain
`e1aChainC`.**

Given `c ∈ Z2loc`, the Shapiro computation `e1a_sha2_mem_deltaRange_gen_iota` applied to the
canonical cover `freeCover N` of `N = DualMod p (E ⊗ T)` and the canonical coefficient
identification `e1aCoeffNat` produces `z ∈ H¹(Γ, Hom_ℤ(R_N, Ωˣ))` with
`e1aDelta z = e1aCoeffMapOf e1aCoeffNat (H2π c)`; the preimage
`y = e1aSyzShift (e1cEquiv.symm z) ∈ Ext²_G(N, Kˣ)` then satisfies
`e1aChainC y = e1aCoeffH2 (e1aDelta z) = H2π c`. -/
theorem e1a_sha2_mem_range_chainC (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
      (hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
        @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
          (DistribMulAction.compHom E (SSGRoute.res k K))),
      c ∈ Work.SSGRoute.Z2loc p k Ω K E →
      ∃ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
          (SSGRoute.PTExt.unitsK k K) 2,
        Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y =
          (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  intro c hZ hc
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    finite_dualMod_tensor p E T
  -- ### the Shapiro computation for the canonical cover
  obtain ⟨z, hz⟩ := e1a_sha2_mem_deltaRange_gen_iota p k Ω K ζ hζ hζK T hT E
      (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V
      (freeCover (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      (freeCover_surjective _)
      (Work.SSGRoute.ExtChain.e1aSES _)
      ((Classical.choose_spec (homCoind_SES (k := k) (Ω := Ω) (K := K)
        (ι := (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V)
        (freeCover _) (freeCover_surjective _))).1)
      (Work.SSGRoute.ExtChain.e1aDelta (k := k) (Ω := Ω) (K := K) _)
      (Work.AbsoluteKummer.SES.range_deltaH2_eq_ker_mapH2 _)
      (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E)
      (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e)
      c hZ hc
  -- ### invert the chain at `z`
  refine ⟨(Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      ((Work.SSGRoute.ExtChain.e1cEquiv (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (freeCover
          (modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))))).symm z), ?_⟩
  show Work.SSGRoute.ExtChain.e1aCoeffH2 p k Ω K ζ hζ hζK T hT E
      (e1aChainH (k := k) (Ω := Ω) (K := K)
        (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
        ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
          (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          ((Work.SSGRoute.ExtChain.e1cEquiv (k := k) (Ω := Ω) (K := K)
            (CategoryTheory.Limits.kernel (freeCover
              (modRep (K ≃ₐ[k] K)
                (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))))).symm z))) =
      (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩)
  rw [e1aChainH_apply]
  rw [show (Work.SSGRoute.ExtChain.e1cEquiv (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (freeCover
          (modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))))
        ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
          (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))).symm
        ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
          (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          ((Work.SSGRoute.ExtChain.e1cEquiv (k := k) (Ω := Ω) (K := K)
            (CategoryTheory.Limits.kernel (freeCover
              (modRep (K ≃ₐ[k] K)
                (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))))).symm z))) = z
      from by rw [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]]
  rw [hz]
  exact e1aCoeffH2_e1aCoeffMapOf_e1aCoeffNat p k Ω K ζ hζ hζK T hT E _

end

end Work.SSGRoute.PT
