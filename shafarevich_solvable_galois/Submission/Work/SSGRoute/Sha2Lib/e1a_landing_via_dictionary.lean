import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.e1a_assembly
import Submission.Work.SSGRoute.PT.e1aBetaCan_aux
import Submission.Work.SSGRoute.PT.e1aBetaCan_localDictionary_fin_compat
import Submission.Work.SSGRoute.PT.e1aBetaCan_splitPlaces
import Submission.Work.SSGRoute.PT.e1aBetaCan_placeExists
import Submission.Work.SSGRoute.extToIdeles_eq_zero_iff_extLoc
import Submission.Work.SSGRoute.glue_infinite_place
import Submission.Work.SSGRoute.PT.e1a_sha2_mem_range_chainC
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
import Submission.Work.SSGRoute.SSGStage.e1aLandingInfLocal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The landing clause of node `E1a`, assembled here

`Work.SSGRoute.SSGStage.e1aLandingClause`
(`Submission/Work/SSGRoute/SSGStage/e1aLandingClause.lean`) is the place-by-place assembly of the
E1a landing clause `im β ⊆ ker extToIdeles` from

* the continuous local condition `e1aBetaCan_akRes_eq_zero` (proved in that file),
* the finite-place dictionary `e1aLandingFinCompat`,
* the archimedean dictionary `e1aLandingInfLocal`.

That file currently does **not** compile: its two uses of the carrier of
`SSGRoute.Z2loc` (`ShaCocycles.lean:380`) carry one projection too many.  The carrier is the
right-nested conjunction

  `IsCocycle2 ∧ IsLocConst2 ∧ (∀ A, ·) ∧ (∀ σ, σ^2 = 1 → ·)`,

so the finite-places clause is `hc.2.2.1` and the involution clause is `hc.2.2.2`; the file writes
`hc.2.2.2.1` and `hc.2.2.2.2`.

This file reproduces the assembly with those two projections corrected, so that the landing clause
is available to consumers *without* depending on the `sorry` of `PT.e1aBetaCan_le_ker`
(`Submission/Work/SSGRoute/PT/e1aBetaCan_le_ker.lean`).  Its axiom closure is then exactly the
closure of the two dictionaries `e1aLandingFinCompat` (i.e. of
`PT.e1aBetaCan_localDictionary_fin_compat`) and `e1aLandingInfLocal` — the *named* remaining
pieces of the E1a lane — rather than an orphan `sorry` that nothing points at.
-/

namespace Work.SSGRoute.SSGStage

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-- **The continuous restriction of the canonical chain is killed by the local conditions.**
(Copy of `Work.SSGRoute.SSGStage.e1aBetaCan_akRes_eq_zero`.) -/
theorem e1aBetaCan_akRes_eq_zero' (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
      (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E).range)
    (b : Work.SSGRoute.Sha2 p k Ω K E) (H : Subgroup (Ω ≃ₐ[k] Ω))
    (hcob : ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E,
      c ∈ Work.SSGRoute.Z2loc p k Ω K E →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c) :
    @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ H E _
      (DistribMulAction.compHom E (SSGRoute.res k K))
      (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E
        (Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b)) = 0 := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  rw [Work.SSGRoute.PT.e1aBetaCan_chainC p k Ω K ζ hζ hζK T hT E hmem b]
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective
    ((Work.SSGRoute.B2top p k Ω K E).comap (Work.SSGRoute.Z2loc p k Ω K E).subtype) b
  have hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c.1 q.1 q.2) ∈
      @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) := by
    rw [Work.AbsoluteKummer.mem_Z2_iff]
    exact ⟨(Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
          (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c.1 q.1 q.2)).mp c.2.1,
      Work.SSGRoute.bridge_isLocConst2_isLocallyConstant (G := K ≃ₐ[k] K)
        (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c.1 q.1 q.2) c.2.2.1⟩
  rw [(Classical.choose_spec (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)).2 c.1 c.2 hZ]
  rw [Work.AbsoluteKummer.akRes_H2π H E
    (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c.1 q.1 q.2) hZ]
  rw [Work.AbsoluteKummer.H2π_eq_zero_iff, Work.AbsoluteKummer.mem_B2_iff]
  obtain ⟨bd, hbdloc, hbdeq⟩ := hcob c.1 c.2
  refine ⟨fun u : ↥H => bd (u : Ω ≃ₐ[k] Ω), ?_, ?_⟩
  · exact Work.SSGRoute.PT.isLocallyConstant_subtype_of_isLocConstOn H hbdloc
  · ext q
    obtain ⟨g, h⟩ := q
    show (g : ↥H) • bd (h : Ω ≃ₐ[k] Ω) - bd ((g * h : ↥H) : Ω ≃ₐ[k] Ω)
        + bd (g : Ω ≃ₐ[k] Ω) = c.1 (g : Ω ≃ₐ[k] Ω) (h : Ω ≃ₐ[k] Ω)
    rw [hbdeq (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2]
    rfl

/-- **Shafarevich's theorem, node `E1a`, landing clause** (the statement of
`Work.SSGRoute.PT.e1aBetaCan_le_ker`, assembled here from the two dictionaries). -/
theorem e1aBetaCan_le_ker_via_landing (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
      (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E).range) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      (∃ b : Work.SSGRoute.Sha2 p k Ω K E,
          Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b = y) →
        SSGRoute.PTExt.extToIdeles y = 0 := by
  intro y hb
  obtain ⟨b, rfl⟩ := hb
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hfinV : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  haveI : Module.Finite ℤ (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.module_finite_int_of_finite (G := K ≃ₐ[k] K) _
  rw [Work.SSGRoute.extToIdeles_eq_zero_iff_extLoc (k := k) (K := ↥K)
    (M := SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b)]
  intro w
  cases w with
  | inl v =>
    rcases SSGRoute.glue_infinite_place k Ω K v with hbot | ⟨σ, hσ2, hle⟩
    · exact Work.SSGRoute.PT.extLoc_extToIdeles_eq_zero_of_decompK_eq_bot
        (K := ↥K) _ _ (NK.GlobalCFT.Place.ofInfinite v) hbot
    · exact Work.SSGRoute.SSGStage.e1aLandingInfLocal p k Ω K ζ hζ hζK T hT E v σ hσ2 hle
        (Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b)
        (e1aBetaCan_akRes_eq_zero' p k Ω K ζ hζ hζK T hT E hmem b (Subgroup.zpowers σ)
          (fun c hc => hc.2.2.2 σ hσ2))
  | inr q =>
    obtain ⟨A, hA, hAq⟩ := SSGRoute.exists_isFinPlace_hAq k Ω K q
    exact Work.SSGRoute.SSGStage.e1aLandingFinCompat p k Ω K ζ hζ hζK T hT E A hA q hAq
      (Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b)
      (e1aBetaCan_akRes_eq_zero' p k Ω K ζ hζ hζK T hT E hmem b (SSGRoute.decomp k A)
        (fun c hc => hc.2.2.1 A hA))

end

end Work.SSGRoute.SSGStage
