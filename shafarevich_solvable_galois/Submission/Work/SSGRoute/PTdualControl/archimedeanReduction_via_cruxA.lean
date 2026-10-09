import Mathlib
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
import Submission.Work.SSGRoute.SSGStage.archimedeanLocalDictionary
import Submission.Work.SSGRoute.PTdualControl.archimedeanLambda_injective_exists
import Submission.Work.SSGRoute.PTdualControl.akToGCH2_zpowers_injective
import Submission.Work.SSGRoute.E1aClean.ArchimedeanOddLanding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean node `E1a` reduced to the archimedean `CRUX-a`

The archimedean half of the `E1a` landing clause is, on disk, the pair

* `Work.SSGRoute.SSGStage.e1aLandingInfLocal` (proved *from* the dictionary), whose statement is the
  **`akRes` form**: `akRes_{⟨σ⟩} (e1aChainC y) = 0 → extLoc_w (extToIdeles y) = 0`, and
* `Work.SSGRoute.SSGStage.archimedeanLocalDictionary` (`sorry`), whose statement is the *stronger*
  **dictionary form**: `∃ Λ` injective with the `akToGCH2`-tainted compatibility clause.

This file records the reduction of the archimedean node to the **archimedean `CRUX-a`**, i.e. to the
archimedean instance of the crux of `PT/NOTE_e1aChainC_localComparison_session12.md` §2,

    resH1_{⟨σ⟩} (e1cEquiv R z) = 0  ⟹  (extRes_{⟨σ̄⟩} z).comp (mk₀ (unitsToLocalUnits)) = 0,

exactly parallel to what the `ExtChain` lane recorded for the *finite* places at
`Work.SSGRoute.ExtChain.e1aLandingFinCompat_via_cruxA` (`SSGRoute/ExtChain/e1aLandingFinCompat_via_cruxA.lean`).
The chain of implications is the same one (`PT/NOTE_e1aChainC_localComparison_session12.md` §1):

    akRes_{⟨σ⟩}(e1aChainC y) = 0
      → resH1_{⟨σ⟩}(e1cEquiv R ((e1aSyzShift N)⁻¹ y)) = 0   [SSGStage.resH1_e1cEquiv_eq_zero_of_akRes_e1aChainC_eq_zero, proved]
      → (extRes_{⟨σ̄⟩} z).comp (mk₀ (unitsToLocalUnits)) = 0  [CRUX-a, the missing archimedean input]
      → extLoc_w (extToIdeles y) = 0                        [SSGStage brick (F), proved]

Consequently the *whole* archimedean node is

* `archimedeanLocalDictionary` ⟸ the `akRes` form (`archimedeanLocalDictionary_of_akResForm`, here),
* the `akRes` form ⟸ the archimedean `CRUX-a` (`e1aLandingInfLocal_via_cruxA`, here),

so the archimedean input of node `E1a` is a *single* named statement, in the same shape as the
finite crux `Work.SSGRoute.PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero`, hence attackable by
the same local-data machinery (the archimedean local data being much simpler: `D_w ≅ ℤ/2` and the
local units `ℂˣ` divisible).  The `toGCH2`-passage in the dictionary form uses
`PTdualControl.akToGCH2_injective_zpowers` (the two models of `H²(⟨σ⟩, ·)` agree, `⟨σ⟩` being
finite and hence discrete).
-/

namespace Work.SSGRoute.PTdualControl

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

attribute [local instance] Work.SSGRoute.freeCoverSES_finite

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The archimedean instance of the `E1a` crux (`CRUX-a` at an infinite place).**

For an infinite place `w` of `K` and an involution `σ ∈ Gal(Ω/k)` whose image contains the
decomposition group `D_w` (`hle`), the vanishing of the restricted `E1c` class
`resH1_{⟨σ⟩} (e1cEquiv R z)` forces the localised degree-one class
`(extRes_{D_w} z).comp (mk₀ (unitsToLocalUnits))` to vanish.

The side conditions `hσ`, `hle` **and `hlink`** are carried here (just as the finite crux carries
`A`, `hA`, `q`, `hAq`).

* `hle : D_w ≤ (⟨σ⟩).map (res k K)`; without it, `σ = 1` makes the restriction hypothesis
  `resH1_⊥ = 0` vacuous while the conclusion is the unconditional localised vanishing
  (cf. `SSGStage.resH1_zpowers_eq_zero_of_res_eq_one`).
* `hlink` is the **seam clause**: `σ` must act on `Ω` through the completion
  `φ = ComplexEmbedding.lift Ω w.embedding` as (local) complex conjugation,
  `φ.comp (σ : Ω →+* Ω) = ComplexEmbedding.conjugate φ`.  This is the archimedean analogue of the
  lying-over clause `hAq` of the finite crux: it is what makes the coefficient change `Ωˣ → K_wˣ`
  `⟨σ⟩`-equivariant, and its absence was **found by a delegated prover to make the crux false**
  (their analysis: the crux is equivalent to "a lift of `(ΨE y)|_H` along `κ` with values in `Ωˣ`
  implies a lift of the local datum along `κ` with values in `K_wˣ`", which cannot hold for an
  involution `σ` not compatible with the place `w` — e.g. for `k = ℚ(√2)`, `K = ℚ(ζ₈)`, the
  involution belonging to the *other* real place of `k` satisfies `hσ` and `hle`).  The compatible
  `σ` is supplied by `PTdualControl.glue_infinite_place_with_link` (delegated), which exposes exactly
  this `hlink` data.

This is the archimedean twin of `Work.SSGRoute.PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero`
(the finite-place crux, on disk as a statement-only `sorry`), and by
`e1aLandingInfLocal_via_cruxA` below it implies the `akRes` form of the archimedean landing clause.
Note that — in contrast with the finite case — the local coefficient here is `K_wˣ = ℂˣ`
(divisible), and `D_w ≅ ℤ/2`, so the local dictionary at `w` is the *divisible-coefficient* one
(`Work.SSGRoute.ext_two_iso_divisible_cohomology`, `archimedeanLambda_injective_exists`). -/
def ArchimedeanCruxA (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hlink : (NumberField.ComplexEmbedding.lift Ω w.embedding).comp (σ : Ω →+* Ω)
      = NumberField.ComplexEmbedding.conjugate
          (NumberField.ComplexEmbedding.lift Ω w.embedding))
    (hle : SSGRoute.PTExt.decompK (k := k) (K := ↥K)
      (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K)) : Prop :=
  ∀ (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [Module.Finite ℤ ↑(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)).V]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
      (SSGRoute.PTExt.unitsK k K) 1),
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (Work.SSGRoute.ExtChain.e1cEquiv
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0 →
      (SSGRoute.PTExt.extRes
          (SSGRoute.PTExt.decompK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofInfinite w)).subtype z).comp
        (CategoryTheory.Abelian.Ext.mk₀
          (NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofInfinite w)))
        (add_zero 1) = 0

/-- **The archimedean landing clause (`akRes` form), from the archimedean crux.**  Statement
verbatim from `Work.SSGRoute.SSGStage.e1aLandingInfLocal`; the extra arguments are the archimedean
crux `ArchimedeanCruxA` and its seam clause `hlink` — note that the on-disk
`SSGStage.e1aLandingInfLocal` *lacks* `hlink` and is therefore mis-stated (see the note
`PTdualControl/NOTE_s14_archimedeanCruxA_and_leaf5_frontier.md` §2bis). -/
theorem e1aLandingInfLocal_via_cruxA (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hlink : (NumberField.ComplexEmbedding.lift Ω w.embedding).comp (σ : Ω →+* Ω)
      = NumberField.ComplexEmbedding.conjugate
          (NumberField.ComplexEmbedding.lift Ω w.embedding))
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K))
    (hcruxA : ArchimedeanCruxA p k Ω K ζ hζ hζK T hT E w σ hσ hlink hle) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ (Subgroup.zpowers σ) E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofInfinite w)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  intro y hy
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  have h1 := Work.SSGRoute.SSGStage.resH1_e1cEquiv_eq_zero_of_akRes_e1aChainC_eq_zero
    p k Ω K ζ hζ hζK T hT E (Subgroup.zpowers σ)
    (isClosed_zpowers (k := k) (Ω := Ω) σ hσ) y hy
  have h2 := hcruxA (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))).symm y) h1
  rw [← AddEquiv.apply_symm_apply (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
    (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))) y]
  exact Work.SSGRoute.SSGStage.extLoc_extToIdeles_e1aSyzShift_eq_zero K
    (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (NK.GlobalCFT.Place.ofInfinite w)
    ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))).symm y) h2

/-- **The archimedean local dictionary from its `akRes` form.**  `archimedeanLocalDictionary` asks
for an *injective* `Λ` together with the `akToGCH2`-tainted compatibility clause; given the (`akRes`)
form of the archimedean landing clause — the conclusion of `e1aLandingInfLocal_via_cruxA` — the
clause follows at once: the inclusion of the two models `akToGCH2 ↥⟨σ⟩` is injective (the involution
group is finite, hence discrete), so `resH2_{⟨σ⟩} (akToGCH2 (e1aChainC y)) = 0` is equivalent to
`akRes_{⟨σ⟩} (e1aChainC y) = 0` by `AbsoluteKummer.akToGCH2_akRes`, and `Λ` may be taken to be the
clause-(A) witness `archimedeanLambda_injective_exists`. -/
theorem archimedeanLocalDictionary_of_akResForm (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K))
    (h : ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ (Subgroup.zpowers σ) E _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofInfinite w)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0) :
    ∃ Λ : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
            (NK.GlobalCFT.Place.ofInfinite w)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)) 2 →+
      @Work.GroupCohomology.H2 ↥(Subgroup.zpowers σ) E _ _
        (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)),
      Function.Injective Λ ∧
      (∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
        @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)
            (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 →
        Λ (SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofInfinite w)
            (SSGRoute.PTExt.extToIdeles (k := k) y)) = 0) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  obtain ⟨Λ, hΛ⟩ := archimedeanLambda_injective_exists p k Ω K ζ hζ hζK T hT E w σ hσ hle
  refine ⟨Λ, hΛ, ?_⟩
  intro y hy
  have key : @Work.AbsoluteKummer.akRes (Ω ≃ₐ[k] Ω) _ _ (Subgroup.zpowers σ) E _
      (DistribMulAction.compHom E (SSGRoute.res k K))
      (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) = 0 := by
    refine akToGCH2_injective_zpowers E σ hσ ?_
    rw [@Work.AbsoluteKummer.akToGCH2_akRes (Ω ≃ₐ[k] Ω) _ _ (Subgroup.zpowers σ) E _
      (DistribMulAction.compHom E (SSGRoute.res k K))
      (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)]
    exact hy
  rw [h y key, map_zero]

/-- **The archimedean local dictionary at an odd prime, unconditionally.**  For `p ≠ 2` the target
`Ext²_{D_w}(E'|, K_wˣ)` of the dictionary is a subsingleton
(`SSGStage.archimedeanExt2Subsingleton`, via `E1aClean.archimedeanLanding_odd`), so `Λ := 0` is
injective and its compatibility clause is vacuous.  Hence the *content* of the archimedean
dictionary — and of the archimedean half of the landing clause — is the `p = 2` case alone. -/
theorem archimedeanLocalDictionary_odd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K)) :
    ∃ Λ : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
            (NK.GlobalCFT.Place.ofInfinite w)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)) 2 →+
      @Work.GroupCohomology.H2 ↥(Subgroup.zpowers σ) E _ _
        (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)),
      Function.Injective Λ ∧
      (∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
        @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)
            (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 →
        Λ (SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofInfinite w)
            (SSGRoute.PTExt.extToIdeles (k := k) y)) = 0) := by
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hMfin : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  haveI : Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
          (NK.GlobalCFT.Place.ofInfinite w)).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)) 2) :=
    Work.SSGRoute.E1aClean.archimedeanExt2Subsingleton p hp2 k ↥K
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
      (fun x => Work.SSGRoute.E1aClean.psmul_e1aCoeff_eq_zero p E T x) w
  exact ⟨0, fun a b _ => Subsingleton.elim a b, fun y _ => by simp⟩

/-- **The archimedean local dictionary from the archimedean crux** (the two reductions composed):
the whole archimedean input of node `E1a` is `ArchimedeanCruxA`. -/
theorem archimedeanLocalDictionary_via_cruxA (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hlink : (NumberField.ComplexEmbedding.lift Ω w.embedding).comp (σ : Ω →+* Ω)
      = NumberField.ComplexEmbedding.conjugate
          (NumberField.ComplexEmbedding.lift Ω w.embedding))
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K))
    (hcruxA : ArchimedeanCruxA p k Ω K ζ hζ hζK T hT E w σ hσ hlink hle) :
    ∃ Λ : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
            (NK.GlobalCFT.Place.ofInfinite w)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)) 2 →+
      @Work.GroupCohomology.H2 ↥(Subgroup.zpowers σ) E _ _
        (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)),
      Function.Injective Λ ∧
      (∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
        @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)
            (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 →
        Λ (SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofInfinite w)
            (SSGRoute.PTExt.extToIdeles (k := k) y)) = 0) :=
  archimedeanLocalDictionary_of_akResForm p k Ω K ζ hζ hζK T hT E w σ hσ hle
    (e1aLandingInfLocal_via_cruxA p k Ω K ζ hζ hζK T hT E w σ hσ hlink hle hcruxA)

/-- **The archimedean local dictionary needs the crux only at `p = 2`.**  For `p ≠ 2` the
dictionary holds unconditionally (`archimedeanLocalDictionary_odd`), so the *whole* archimedean
input of node `E1a` is `ArchimedeanCruxA` at the single prime `p = 2` — where `T` is trivial, `M` is
the `𝔽₂`-dual of `E`, `D_w ≅ ℤ/2` and `K_wˣ = ℂˣ` is divisible. -/
theorem archimedeanLocalDictionary_of_crux_two (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hlink : (NumberField.ComplexEmbedding.lift Ω w.embedding).comp (σ : Ω →+* Ω)
      = NumberField.ComplexEmbedding.conjugate
          (NumberField.ComplexEmbedding.lift Ω w.embedding))
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K))
    (hcrux : p = 2 → ArchimedeanCruxA p k Ω K ζ hζ hζK T hT E w σ hσ hlink hle) :
    ∃ Λ : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
            (NK.GlobalCFT.Place.ofInfinite w)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)) 2 →+
      @Work.GroupCohomology.H2 ↥(Subgroup.zpowers σ) E _ _
        (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)),
      Function.Injective Λ ∧
      (∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
        @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)
            (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 →
        Λ (SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofInfinite w)
            (SSGRoute.PTExt.extToIdeles (k := k) y)) = 0) := by
  rcases eq_or_ne p 2 with h2 | h2
  · exact archimedeanLocalDictionary_via_cruxA p k Ω K ζ hζ hζK T hT E w σ hσ hlink hle (hcrux h2)
  · exact archimedeanLocalDictionary_odd p h2 k Ω K ζ hζ hζK T hT E w σ hσ hle

end

end Work.SSGRoute.PTdualControl
