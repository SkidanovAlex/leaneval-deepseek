import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.e1aBetaCan_aux
import Submission.Work.SSGRoute.PT.e1aBetaCan_splitPlaces
import Submission.Work.SSGRoute.PT.e1aBetaCan_placeExists
import Submission.Work.SSGRoute.extToIdeles_eq_zero_iff_extLoc
import Submission.Work.SSGRoute.PT.e1a_localComparison_bricks
import Submission.Work.SSGRoute.PT.e1a_sha2_mem_range_chainC
import Submission.Work.SSGRoute.ExtChain.freeCoverSES_lattice
import Submission.Work.SSGRoute.PTdualControl.akToGCH2_zpowers_injective
import Submission.Work.SSGRoute.PTdualControl.glue_infinite_place_with_link
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.E1aClean.archimedeanKillClauseLinked
import Submission.Work.SSGRoute.E1aClean.ArchimedeanOddLanding
import Submission.Work.SSGRoute.E1aClean.landingFinCompat_from_criterion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The E1a landing clause, sorry-free modulo the finite-place criterion

This is the place-by-place assembly of Shafarevich's theorem node `E1a`, i.e. of

  `im β ⊆ ker extToIdeles`,   `β = PT.e1aBetaCan`,

in the exact form of `Work.SSGRoute.SSGStage.e1aBetaCan_le_ker_via_landing`
(`Sha2Lib/e1a_landing_via_dictionary.lean`), with the two local leaves wired to *proved* statements:

* **archimedean places** (`inl v`).  The bare archimedean leaf
  `SSGStage.e1aLandingInfLocal` is not provable as stated (its hypothesis is a vanishing in
  `H¹(⟨σ⟩, ·)` which depends on the chosen lift `σ` of `res k K σ`; see
  `E1aClean/NOTE_infLocalCriterion_frontier.md` §4 and `E1aClean/akResZpowersChainCImmaterial.lean`).
  The *correct* statement carries the **seam** (the link `φ ∘ σ = conj ∘ φ`), and it is *proved*:
  `E1aClean.archimedeanKillClauseLinked`.  The seam data is supplied by
  `PTdualControl.glue_infinite_place_with_link`, which exposes the link already constructed inside
  `glue_infinite_place`.  Crucially the *same* `σ` produced there is used for the hypothesis —
  which is legitimate because the archimedean clause `hc.2.2.2` of `Z2loc` quantifies over *all*
  involutions `σ` of `Gal(Ω/k)` — so no immateriality in the lift is needed.
* **finite places** (`inr q`).  The leaf is `E1aClean.e1aLandingFinCompat_of_criterion`
  (`E1aClean/landingFinCompat_from_criterion.lean`), which derives the finite-place landing clause
  from the sharp per-place criterion `E1aClean.finLocalCriterion`.  That criterion is the single
  remaining input of the whole node.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

-- The finiteness of the canonical syzygy `ker (freeCover X)` from the finiteness of `X`.
attribute [local instance] Work.SSGRoute.freeCoverSES_finite

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

/-- **Shafarevich's theorem, node `E1a`, landing clause** — the place-by-place assembly with the
archimedean leaf replaced by the *seam-carrying* (and proved) clause and the finite leaf by the
criterion `E1aClean.finLocalCriterion`.  Statement identical to
`Work.SSGRoute.SSGStage.e1aBetaCan_le_ker_via_landing`. -/
theorem e1aBetaCan_le_ker_clean (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
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
  haveI hNfin : Finite (SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  rw [Work.SSGRoute.extToIdeles_eq_zero_iff_extLoc (k := k) (K := ↥K)
    (M := SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b)]
  intro w
  -- the class whose localisations are at stake: `β_E b` (the `rfl`-pattern above replaced `y` by it)
  set Y := Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b with hY
  cases w with
  | inl v =>
    -- ## the archimedean place
    by_cases hbot : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite v) = ⊥
    · -- trivial decomposition group: the localised class vanishes unconditionally
      exact Work.SSGRoute.PT.extLoc_extToIdeles_eq_zero_of_decompK_eq_bot
        (K := ↥K) _ _ (NK.GlobalCFT.Place.ofInfinite v) hbot
    · -- non-trivial decomposition group: use the *linked* involution produced by the glue lemma
      obtain ⟨σ, hσ2, hσlink, hle⟩ :=
        (Work.SSGRoute.PTdualControl.glue_infinite_place_with_link k Ω K v).resolve_left hbot
      -- the vanishing of the `E1c`-dictionary class at the linked involution, from `Z2loc`
      have h1 : Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
          (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel
            (Work.SSGRoute.freeCover (SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
          (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
            (CategoryTheory.Limits.kernel
              (Work.SSGRoute.freeCover (SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
            ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
              (SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm Y)) = 0 :=
        Work.SSGRoute.SSGStage.resH1_e1cEquiv_eq_zero_of_akRes_e1aChainC_eq_zero
          p k Ω K ζ hζ hζK T hT E (Subgroup.zpowers σ)
          (Work.SSGRoute.PTdualControl.isClosed_zpowers (k := k) (Ω := Ω) σ hσ2) Y
          (e1aBetaCan_akRes_eq_zero' p k Ω K ζ hζ hζK T hT E hmem b (Subgroup.zpowers σ)
            (fun c hc => hc.2.2.2 σ hσ2))
      -- the seam-carrying archimedean kill clause
      have h2 := archimedeanKillClauseLinked (k := k) (Ω := Ω) K v σ hσ2
        (NumberField.ComplexEmbedding.lift Ω v.embedding)
        (fun z => NumberField.ComplexEmbedding.lift_algebraMap_apply Ω v.embedding z)
        (fun x => RingHom.congr_fun hσlink x) hle
        (SSGRoute.SSGStage.e1aN0 p k Ω K T E) _ h1
      -- the degree reduction
      have h3 := Work.SSGRoute.SSGStage.extLoc_extToIdeles_e1aSyzShift_eq_zero (k := k) K
        (SSGRoute.SSGStage.e1aN0 p k Ω K T E) (NK.GlobalCFT.Place.ofInfinite v) _ h2
      rw [AddEquiv.apply_symm_apply] at h3
      exact h3
  | inr q =>
    -- ## the finite place
    obtain ⟨A, hA, hAq⟩ := SSGRoute.exists_isFinPlace_hAq k Ω K q
    exact e1aLandingFinCompat_of_criterion p k Ω K ζ hζ hζK T hT E A hA q hAq Y
      (e1aBetaCan_akRes_eq_zero' p k Ω K ζ hζ hζK T hT E hmem b (SSGRoute.decomp k A)
        (fun c hc => hc.2.2.1 A hA))

end

end Work.SSGRoute.E1aClean
