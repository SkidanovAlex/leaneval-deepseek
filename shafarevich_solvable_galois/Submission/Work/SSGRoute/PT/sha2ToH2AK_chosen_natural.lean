import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PT.e1a_can_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: naturality of the chosen cocycle-side bridge `Ш²(k,M) → H²_c(G_k,M)`

`Work.SSGRoute.PT.sha2_to_H2AK` produces the bridge
`φ_M := Classical.choose (sha2_to_H2AK p k Ω K M) : Ш²(k,M) →+ H²_c(G_k,M)`, and every element of
`Ш²` is the class of a locally trivial `2`-cocycle, so `φ_M` is *uniquely* determined by the
computation rule that `sha2_to_H2AK` proves for it (`Classical.choose_spec`).  Consequently the
`Classical.choose`-incoherence that makes `e1aBeta` non-natural in `E` does not affect the bridge:
the square

`Ш²(k,M) --Sha2Map f--> Ш²(k,M₂)`
`   | φ_M                          | φ_{M₂}`
`H²(G_k,M) --mapH2 f--> H²(G_k,M₂)`

commutes for *every* equivariant `f`, which is what the naturality clause of
`Work.SSGRoute.PT.e1a_ext_sha2_bridge` needs.  The proof is the argument of
`Work.SSGRoute.sha2ToH2_natural` redone for the `Work.AbsoluteKummer.H2` flavour.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-- **Naturality of the chosen cocycle-side bridge** in the coefficient module. -/
theorem sha2ToH2AK_chosen_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    (b : Work.SSGRoute.Sha2 p k Ω K M) :
    (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K M₂))
        (Work.SSGRoute.Sha2Map p k Ω K M M₂ f hf b)
      = e1aH2Map p k Ω K M M₂ f hf
          ((Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K M)) b) := by
  classical
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M₂ := DistribMulAction.compHom M₂ (SSGRoute.res k K)
  -- the computation rules of the two chosen bridges
  have h₁ := (Classical.choose_spec (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K M)).2
  have h₂ := (Classical.choose_spec (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K M₂)).2
  -- reduce `b` to a representative
  refine Submodule.Quotient.induction_on
    ((Work.SSGRoute.B2top p k Ω K M).comap (Work.SSGRoute.Z2loc p k Ω K M).subtype) b
    fun x => ?_
  -- the two memberships in the *continuous* `2`-cocycles
  have hZpush : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) =>
        Work.SSGRoute.pushC2 p k Ω K M M₂ f x.1 q.1 q.2) ∈
      @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) M₂ _ _ _
        (DistribMulAction.compHom M₂ (SSGRoute.res k K)) := by
    rw [Work.AbsoluteKummer.mem_Z2_iff]
    exact ⟨(Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
        (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) =>
          Work.SSGRoute.pushC2 p k Ω K M M₂ f x.1 q.1 q.2)).mp
        (Work.SSGRoute.Z2loc_pushC2_mem p k Ω K M M₂ f hf x.1 x.2).1,
      Work.SSGRoute.bridge_isLocConst2_isLocallyConstant (G := K ≃ₐ[k] K)
        (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) =>
          Work.SSGRoute.pushC2 p k Ω K M M₂ f x.1 q.1 q.2)
        (Work.SSGRoute.Z2loc_pushC2_mem p k Ω K M M₂ f hf x.1 x.2).2.1⟩
  have hZx : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2) ∈
      @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) M _ _ _
        (DistribMulAction.compHom M (SSGRoute.res k K)) := by
    rw [Work.AbsoluteKummer.mem_Z2_iff]
    exact ⟨(Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
        (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2)).mp x.2.1,
      Work.SSGRoute.bridge_isLocConst2_isLocallyConstant (G := K ≃ₐ[k] K)
        (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2) x.2.2.1⟩
  rw [Work.SSGRoute.Sha2Map_mk p k Ω K M M₂ f hf x,
    h₂ (Work.SSGRoute.pushC2 p k Ω K M M₂ f x.1)
      (Work.SSGRoute.Z2loc_pushC2_mem p k Ω K M M₂ f hf x.1 x.2) hZpush,
    h₁ x.1 x.2 hZx]
  -- both sides are now `H²π` of (definitionally) the same `2`-cocycle
  exact e1aH2Map_H2π p k Ω K M M₂ f hf ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2, hZx⟩
    hZpush

end

end Work.SSGRoute.PT
