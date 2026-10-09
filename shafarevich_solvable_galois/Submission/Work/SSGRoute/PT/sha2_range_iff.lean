import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.e1aBetaCan_range_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `e1aBetaCan_image`: the two provable steps, and the exact remaining input

`PT/NOTE_e1aBetaCan_image_analysis.md` records that the target `PT/e1aBetaCan_image` is equivalent
to the E1a image clause `range φ = e1aChainC '' ker extToIdeles`, and that its proof splits into

* **(step 1, proved in `PT/e1aBetaCan_range_iff.lean`)** `(∃ b, e1aBetaCan … b = y) ↔
  e1aChainC … y ∈ range φ`;
* **(step 2, proved here)** `z ∈ range φ` iff `z = H2π c` for *some* locally trivial continuous
  `2`-cocycle `c ∈ Z2loc` — immediate from the computation rule of `sha2_to_H2AK`;
* **(the crux, *not* on disk)** the chain–localisation comparison
  `extToIdeles y = 0 ↔ ∃ c ∈ Z2loc, H2π c = e1aChainC … y`
  (equivalently: the degree-two local dictionary `Ext²_{D_w}(res E',K_wˣ) ≅ H²(D_A,E)` commuting with
  `extLoc ∘ extToIdeles` and with `e1aChainC`; see the note, §3).

`e1aBetaCan_image_of_extToIdeles_iff` below is the *assembly*: it proves the target from the crux,
with the crux as an explicit hypothesis.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

/-- The continuous `2`-cocycle in `Work.AbsoluteKummer.Z2` attached to a locally trivial
`2`-cocycle, i.e. an element of `SSGRoute.Z2loc`: the two membership fields are transported by the
bridges `bridge_isCocycle2_mem_Z2` / `bridge_isLocConst2_isLocallyConstant`. -/
noncomputable def Z2ofZ2loc (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (c : ↥(Work.SSGRoute.Z2loc p k Ω K E)) :
    @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
      (DistribMulAction.compHom E (SSGRoute.res k K)) :=
  ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c.1 q.1 q.2, by
    letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
    rw [Work.AbsoluteKummer.mem_Z2_iff]
    exact ⟨(Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
          (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c.1 q.1 q.2)).mp c.2.1,
      Work.SSGRoute.bridge_isLocConst2_isLocallyConstant (G := K ≃ₐ[k] K)
        (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c.1 q.1 q.2) c.2.2.1⟩⟩

/-- **Step 2.** The range of the bridge `φ = Classical.choose (sha2_to_H2AK p k Ω K E)`, described by
locally trivial representatives: `z ∈ range φ` iff `z = H2π (Z2ofZ2loc c)` for some `c ∈ Z2loc`.

This is the degree-two analogue of `sha1_descent_range`, and it is immediate from the computation
rule in `sha2_to_H2AK` together with `Sha2 = Z2loc ⧸ B2top`. -/
theorem sha2_range_iff (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ∀ z : @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)),
      z ∈ (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)).range ↔
        ∃ c : ↥(Work.SSGRoute.Z2loc p k Ω K E),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)) (Z2ofZ2loc p k Ω K E c) = z := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  intro z
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective
      ((Work.SSGRoute.B2top p k Ω K E).comap (Work.SSGRoute.Z2loc p k Ω K E).subtype) b
    refine ⟨c, ?_⟩
    have hrule := (Classical.choose_spec
      (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)).2 c.1 c.2 (Z2ofZ2loc p k Ω K E c).2
    simpa only [Z2ofZ2loc] using hrule.symm
  · rintro ⟨c, hc⟩
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    have hrule := (Classical.choose_spec
      (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)).2 c.1 c.2 (Z2ofZ2loc p k Ω K E c).2
    simpa only [Z2ofZ2loc] using hrule.trans hc

/-- **The assembly: the target from the crux.**  The only unproved input is the chain–localisation
comparison `hC` (the degree-two local dictionary, see `PT/NOTE_e1aBetaCan_image_analysis.md` §3);
everything else is `e1aBetaCan_eq_iff_chainC_mem_range` (step 1) and `sha2_range_iff` (step 2). -/
theorem e1aBetaCan_image_of_extToIdeles_iff (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
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
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E).range)
    (hC : ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      SSGRoute.PTExt.extToIdeles y = 0 ↔
        ∃ c : ↥(Work.SSGRoute.Z2loc p k Ω K E),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)) (Z2ofZ2loc p k Ω K E c) =
              Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      (∃ b : Work.SSGRoute.Sha2 p k Ω K E,
          Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b = y) ↔
        SSGRoute.PTExt.extToIdeles y = 0 := by
  intro y
  rw [e1aBetaCan_eq_iff_chainC_mem_range p k Ω K ζ hζ hζK T hT E hmem y]
  rw [sha2_range_iff p k Ω K E (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)]
  exact (hC y).symm

end

end Work.SSGRoute.PT
