import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.e1aBetaCan_localDictionary_fin_compat
import Submission.Work.SSGRoute.PT.e1aBetaCan_splitPlaces
import Submission.Work.SSGRoute.glue_infinite_place
import Submission.Work.SSGRoute.SSGStage.archimedeanLocalDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean local landing clause of node E1a -- and the seam defect of its statement

## STATUS (2026-10-02): the statement of `e1aLandingInfLocal` is MIS-STATED

The hypotheses `hσ : σ ^ 2 = 1` and `hle : decompK (ofInfinite w) ≤ (zpowers σ).map (res k K)` do
**not** tie the involution `σ` to the place `w`: `(zpowers σ).map (res k K)` only sees the image of
`σ` in `Gal(K/k)`, so involutions belonging to *different* real places of the base field `k` (whose
restrictions to `K` agree) satisfy both, while their local data sit at different places.  The
conclusion `extLoc (ofInfinite w) (extToIdeles y) = 0`, on the other hand, is about the completion
`K_wˣ`, linked to the algebraic-closure coefficient `Ωˣ` used by `e1aChainC` only through the
completion seam

  `hlink : (NumberField.ComplexEmbedding.lift Ω w.embedding).comp (σ : Ω →+* Ω) =
             NumberField.ComplexEmbedding.conjugate (NumberField.ComplexEmbedding.lift Ω w.embedding)`,

the archimedean analogue of the lying-over clause `hAq` carried by the finite-place sibling
`SSGStage.e1aLandingFinCompat`.  Proposed counterexample: `k = ℚ(√2)`, `K = ℚ(ζ₈)`, `w` complex over
one real place of `k`, `σ` the involution of the *other* real place of `k`.

This is recorded in the workspace by the `PTdualControl` lane:

* `ACTION_archimedean_node_seam_defect.md` (root) -- "the archimedean node of leaf `E1a` is
  mis-stated -- it needs the seam clause";
* `Submission/Work/SSGRoute/PTdualControl/PING_archimedeanCruxA.md` §1bis -- a delegated prover
  declared the `hσ`/`hle` crux **FALSE**; "`SSGStage.e1aLandingInfLocal` ... [is] mis-stated as
  written (they range over incompatible `σ`'s) -- this is a statement-design defect, not a hard
  proof";
* the *corrected* statements (one extra hypothesis `hlink`) are on disk and proved axiom-clean in
  `Submission/Work/SSGRoute/PTdualControl/archimedeanReduction_via_cruxA.lean`
  (`ArchimedeanCruxA`, `e1aLandingInfLocal_via_cruxA`, `archimedeanLocalDictionary_via_cruxA`,
  `archimedeanLocalDictionary_odd`, `archimedeanLocalDictionary_of_crux_two`), together with
  `PTdualControl.glue_infinite_place_with_link` (the seam conjunct, proved).

Precedent inside the project: the *finite* sibling with a `≤`-hypothesis but without the lying-over
clause `hAq` was likewise declared FALSE (`PT/NOTE_e1aBetaCan_le_ker.md` §4).

## What this file contains

* `resH2_akToGCH2_e1aChainC_eq_zero_of_akRes_eq_zero` -- **proved here**: the transfer of the
  landing hypothesis from the continuous model (`akRes`) to the abstract model (`resH2`), via
  `akToGCH2_akRes`.  This is the formal step shared by every form of the archimedean clause.
* `e1aLandingInfLocal` -- the statement as requested, proved *conditionally* on the archimedean
  comparison square `SSGStage.archimedeanLocalDictionary` (which its own prover declared false for
  the missing seam; the derivation below is the correct assembly of the two, and is what the
  corrected statement `PTdualControl.e1aLandingInfLocal_via_cruxA` carries out with the seam).
-/

namespace Work.SSGRoute.SSGStage

open CategoryTheory

open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

/-- **The transfer of the landing hypothesis to the abstract model.**  For any subgroup `H` of
`G_k = Ω ≃ₐ[k] Ω` and any class `y` in `Ext²_{Gal(K/k)}(E', Kˣ)`, the vanishing of the *continuous*
restriction `akRes_H (e1aChainC y)` forces the vanishing of the *abstract* restriction
`resH2_H (akToGCH2 (e1aChainC y))` of the forgetful image.

This is `akToGCH2_akRes` (the naturality of the forgetful map with the subgroup restriction)
applied to the hypothesis. -/
theorem resH2_akToGCH2_e1aChainC_eq_zero_of_akRes_eq_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (σ : Ω ≃ₐ[k] Ω)
    (y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2) :
    @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ (Subgroup.zpowers σ) E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 →
      @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)
        (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
          (DistribMulAction.compHom E (SSGRoute.res k K))
          (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 := by
  intro hy
  rw [← @Work.AbsoluteKummer.akToGCH2_akRes (Ω ≃ₐ[k] Ω) _ _
    (Subgroup.zpowers σ) E _ (DistribMulAction.compHom E (SSGRoute.res k K))
    (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y), hy, map_zero]

theorem e1aLandingInfLocal (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K)) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ (Subgroup.zpowers σ) E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofInfinite w)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  intro y hy
  obtain ⟨Λ, hΛinj, hΛ⟩ :=
    archimedeanLocalDictionary p k Ω K ζ hζ hζK T hT E w σ hσ hle
  have htransfer :=
    resH2_akToGCH2_e1aChainC_eq_zero_of_akRes_eq_zero p k Ω K ζ hζ hζK T hT E σ y hy
  exact hΛinj (by rw [hΛ y htransfer, map_zero])

end Work.SSGRoute.SSGStage
