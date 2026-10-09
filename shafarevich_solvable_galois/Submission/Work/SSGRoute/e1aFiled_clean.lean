import Mathlib
import Submission.Work.SSGRoute.PTembedding.G5Core
import Submission.Work.SSGRoute.PT.e1a_assembly
import Submission.Work.SSGRoute.PT.e1a_sha2_mem_range_chainC
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.e1aBetaCan_splitPlaces
import Submission.Work.SSGRoute.PT.e1aChainC_localComparison
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.Sha2Lib.pt_core_assembly
import Submission.Work.SSGRoute.PT.e1aBetaCan_le_ker
-- The landing clause, assembled *sorry-free* from the two named local dictionaries
-- (`SSGStage.e1aLandingFinCompat`, `SSGStage.e1aLandingInfLocal`) rather than from the orphan
-- `sorry` of `PT/e1aBetaCan_le_ker.lean` (which nothing points at).  See
-- `E1aClean/NOTE_session13_route_blocked.md` §0.
import Submission.Work.SSGRoute.Sha2Lib.e1a_landing_via_dictionary
import Submission.Work.SSGRoute.E1aClean.ArchimedeanOdd
import Submission.Work.SSGRoute.E1aClean.ArchimedeanOddLanding
-- The landing clause with the *proved* seam-carrying archimedean leaf
-- (`E1aClean.archimedeanKillClauseLinked` + `PTdualControl.glue_infinite_place_with_link`) and the
-- finite leaf wired to the local criterion (`E1aClean.finLocalCriterion`).
import Submission.Work.SSGRoute.E1aClean.e1aBetaCan_le_ker_clean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Node `E1a`, in the form the atom's assembly consumes** (the reviewers' recommendation:
target `G5Core.E1aInput`, not `E1aFiled`).  `Work.SSGRoute.G5Core.E1aInput p k Ω K T` is: there is
a family `β_E : Ш²(k,E) →+ Ext²_G(E^∨(1), Kˣ)` (`E^∨(1) = DualMod p (E ⊗ T)`), injective for every
finite `E`, **landing** in `ker extToIdeles` (for every `b` there is
`x ∈ Ext¹_G(E^∨(1),C_K)` with `extDelta x = β_E b`), and natural in `E`.

This is the first arithmetic input of `Work.SSGRoute.tatePoitouEmbedding` (see
`Submission/Work/SSGRoute/DESIGN_FIX2.md` §6, §10).  The filed `Work.SSGRoute.ext_sha2_bridge`
proves the *stronger* `E1aFiled` (with the `↔`) but has three `sorry`s, which propagate `sorryAx`
into the atom's axiom closure; this node asks for a `sorry`-free proof of the consumed form.

Guidance (all paths here are **cycle-free w.r.t. the atom** — import them, but do NOT import the
atom `Submission.Work.SSGRoute.tatePoitouEmbedding` or anything that imports it, i.e. not
`PTembedding.tatePoitouEmbedding_alt`, `PTembedding.ptAssembly`, `stage_global_lifting`,
`sha2_image_of_Hm2`, `PTdualControl.sha2_dual_control_alt`, `ValuationSES.E9Input_of_core`, since
the atom must be able to import *your* module).

* The canonical `β` is `PT.e1aBetaCan` (`Submission/Work/SSGRoute/PT/e1a_beta_can.lean`), which is
  the inverse (along `PT.e1aChainC`) of `PT.sha2_to_H2AK` restricted to the range; its injectivity is
  `PT.e1aBetaCan_injective`, its naturality `PT.e1aBetaCan_natural`, its computation rule
  `PT.e1aBetaCan_chainC` — all clean.  The range hypothesis `hmem` is supplied cleanly by
  `PT.e1aChainC_mem_range` (`PT/e1a_assembly.lean`), whose `hcr` input is
  `PT.e1a_sha2_mem_range_chainC` (`PT/e1a_sha2_mem_range_chainC.lean`, clean).
* The **landing clause** is the only remaining content: for `y` in the range of `e1aBetaCan` one
  needs `extToIdeles y = 0`, i.e. `extLoc w (extToIdeles y) = 0` at every place `w` (the injectivity
  half of `ext_idele_shapiro`, clean).  The clean place-by-place input for places whose
  decomposition group is trivial is `PT.extLoc_extToIdeles_eq_zero_of_decompK_eq_bot`
  (`PT/e1aBetaCan_splitPlaces.lean`); the general place is `PT.e1aChainC_localComparison`
  (`PT/e1aChainC_localComparison.lean`) together with the `localDictionary` files
  (`PT/e1aBetaCan_localDictionary_fin_compat.lean`, `PT/e1aBetaCan_localDictionary_fin_inj.lean`,
  which still contain a few `sorry`s that must be filled — that is the crux of this node).
  `PT.e1aBetaCan_le_ker` (`PT/e1aBetaCan_le_ker.lean`, one `sorry`) is exactly this statement.
* Once `extToIdeles y = 0` is known, the landing clause follows from
  `Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero`
  (`PTdualControl/extExact.lean`, clean). -/
theorem e1aFiled_clean (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    Work.SSGRoute.G5Core.E1aInput p k Ω K T := by
  classical
  haveI : NumberField ↥K := NumberField.of_module_finite (K := k) (L := ↥K)
  -- the membership clause `hmem` of the canonical map `β`, from the arithmetic crux `hcr`
  have hcr : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
        (hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
          @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))),
        c ∈ Work.SSGRoute.Z2loc p k Ω K E →
        ∃ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
          Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y =
            (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩) :=
    fun E _ _ _ _ _ => Work.SSGRoute.PT.e1a_sha2_mem_range_chainC p k Ω K ζ hζ hζK T hT E
  refine ⟨fun E _ _ _ _ _ =>
      Work.SSGRoute.PT.e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E, ?_, ?_, ?_⟩
  · intro E _ _ _ _ _
    exact Work.SSGRoute.PT.e1aBetaFamily_injective p k Ω K ζ hζ hζK T hT hcr E
  · intro E _ _ _ _ _ b
    refine Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero (k := k)
      (K := ↥K) ((Work.SSGRoute.PT.e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E) b) ?_
    exact Work.SSGRoute.E1aClean.e1aBetaCan_le_ker_clean p k Ω K ζ hζ hζK T hT E
      (Work.SSGRoute.PT.e1aChainC_mem_range p k Ω K ζ hζ hζK T hT E (hcr E))
      ((Work.SSGRoute.PT.e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E) b) ⟨b, rfl⟩
  · intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf F hF b
    exact Work.SSGRoute.PT.e1aBetaFamily_natural p k Ω K ζ hζ hζK T hT hcr E₁ E₂ f hf F hF b

end Work.SSGRoute
