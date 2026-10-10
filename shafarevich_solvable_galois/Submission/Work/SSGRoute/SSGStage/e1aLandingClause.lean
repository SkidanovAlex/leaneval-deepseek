import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ExtChain.e1aLandingFinCompat_via_cruxA
import Submission.Work.SSGRoute.PT.e1a_sha2_mem_range_chainC
import Submission.Work.SSGRoute.PTdualControl.archimedeanCruxA
import Submission.Work.SSGRoute.extToIdeles_eq_zero_iff_extLoc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The landing clause of node `E1a` (`im β ⊆ ker extToIdeles`)

This file proves `Work.SSGRoute.SSGStage.e1aLandingClause`: for a class `y` in the image of the
canonical map `β = e1aBetaCan` of `PT/e1a_beta_can.lean`, the idèle localisation vanishes,
`extToIdeles y = 0`.

The statement is *verbatim* the leaf `E1a` of the arithmetic core
(`Work.SSGRoute.PT.e1aBetaCan_le_ker`), and it is assembled from the *cruxes* of the lane, both
proved in the workspace:

* **the continuous local condition** `e1aBetaCan_akRes_eq_zero` (proved in this file): for
  `y = e1aBetaCan … b` the continuous restriction `akRes_H (e1aChainC y)` vanishes for every
  subgroup `H ≤ Gal(Ω/k)` on which the locally trivial `2`-cocycles representing `b` are
  coboundaries — in particular for the decomposition groups `decomp k A` of the finite places
  (`Z2loc`) and for the groups `⟨σ⟩` of the involutions;
* **the finite-place crux**
  `Work.SSGRoute.PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero` (proved in
  `PT/extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero.lean`, via `E1aClean.finLocalCriterion`):
  the per-place comparison of the canonical chain with the idèle localisation at a finite place;
* **the archimedean crux** `Work.SSGRoute.PTdualControl.archimedeanCruxA`, *with the completion
  seam* `hlink` supplied by the proved place glue
  `Work.SSGRoute.PTdualControl.glue_infinite_place_with_link` (the seam conjunct is the one already
  built inside `glue_infinite_place`; without it the link-free form is false).

The assembly `Work.SSGRoute.PTdualControl.e1aBetaCan_le_ker_via_cruxA` performs the place-by-place
gluing (the localisation criterion `extToIdeles_eq_zero_iff_extLoc`, the split places
`extLoc_extToIdeles_eq_zero_of_decompK_eq_bot`, and the place glue `exists_isFinPlace_hAq` /
`glue_infinite_place_with_link`); we feed it the proved finite crux.
-/

namespace Work.SSGRoute.SSGStage

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

-- The finiteness of the canonical syzygy `ker(freeCover N)` from finiteness of `N`, the local
-- instance registration that the finite-place crux route relies on.
attribute [local instance] Work.SSGRoute.freeCoverSES_finite

/-- **The continuous restriction of the canonical chain is killed by the local conditions.**

For any subgroup `H ≤ Gal(Ω/k)` on which every locally trivial `2`-cocycle is a coboundary, the
restriction `akRes_H` of the canonical chain to `H` vanishes on the classes in the image of
`e1aBetaCan`.  The representing cocycle of `φ b = e1aChainC (e1aBetaCan b)` is the locally trivial
cocycle `c ∈ Z2loc` of `b`, and the local condition at `H` is precisely a primitive of `c|_H` which
is locally constant on `H`; the class of `c|_H` in the continuous cohomology `H²_c(H,E)` is then
zero. -/
theorem e1aBetaCan_akRes_eq_zero (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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

/-- **Shafarevich's theorem, node `E1a`, landing clause**: a class in the image of the canonical map
`β = e1aBetaCan` is killed by the idèle localisation `extToIdeles`.

Equivalently, `im β ⊆ ker(extToIdeles) = im(extDelta)`, i.e. the arithmetic of `Ш²(k,E)` captured
by the canonical chain lands in the Selmer (locally trivial) subgroup of `Ext²_G(E',Kˣ)`.

This is the place-by-place assembly of `PTdualControl.e1aBetaCan_le_ker_via_cruxA`, fed with the
proved finite-place crux `PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero`; the archimedean
places are handled by the proved archimedean crux together with the seam-carrying place glue. -/
theorem e1aLandingClause (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
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
    rcases Work.SSGRoute.PTdualControl.glue_infinite_place_with_link k Ω K v with
      hbot | ⟨σ, hσ2, hlink, hle⟩
    · exact Work.SSGRoute.PT.extLoc_extToIdeles_eq_zero_of_decompK_eq_bot
        (K := ↥K) _ _ (NK.GlobalCFT.Place.ofInfinite v) hbot
    · exact Work.SSGRoute.PTdualControl.e1aLandingInfLocal_via_cruxA p k Ω K ζ hζ hζK T hT E
        v σ hσ2 hlink hle
        (Work.SSGRoute.PTdualControl.archimedeanCruxA p k Ω K ζ hζ hζK T hT E v σ hσ2 hlink hle)
        (Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b)
        (e1aBetaCan_akRes_eq_zero p k Ω K ζ hζ hζK T hT E hmem b (Subgroup.zpowers σ)
          (fun c hc => hc.2.2.2 σ hσ2))
  | inr q =>
    obtain ⟨A, hA, hAq⟩ := SSGRoute.exists_isFinPlace_hAq k Ω K q
    exact Work.SSGRoute.ExtChain.e1aLandingFinCompat_via_cruxA p k Ω K ζ hζ hζK T hT E A hA q hAq
      (fun N _ _ z =>
        Work.SSGRoute.PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero k Ω K N A hA q hAq z)
      (Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b)
      (e1aBetaCan_akRes_eq_zero p k Ω K ζ hζ hζK T hT E hmem b (SSGRoute.decomp k A)
        (fun c hc => hc.2.2.1 A hA))

end

end Work.SSGRoute.SSGStage
