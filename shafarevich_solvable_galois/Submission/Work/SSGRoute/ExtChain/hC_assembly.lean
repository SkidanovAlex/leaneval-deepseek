import Mathlib
import Submission.Work.SSGRoute.PT.sha2_range_iff
import Submission.Work.SSGRoute.PT.e1a_assembly
import Submission.Work.SSGRoute.PT.e1a_sha2_mem_range_chainC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `ext_sha2_bridge`: the node, wired down to two explicit interfaces

This module records the **exact final wiring** of `Work.SSGRoute.ext_sha2_bridge` and reduces it to
two named interfaces, so that the node file becomes a one-line application the moment both are
sorry-free.

## The two interfaces

For `E` with its `Gal(K/k)`-module structure and `hmem` the arithmetic membership clause
(`PT.e1a_sha2_mem_range_chainC`, proved / sorry-free):

* `hland` — the *landing clause* (`im β ⊆ ker extToIdeles`), i.e.
  `(∃ b, e1aBetaCan … hmem b = y) → extToIdeles y = 0`.
  On disk as `Work.SSGRoute.SSGStage.e1aLandingClause` (assembled from `e1aLandingFinCompat`,
  `e1aLandingInfLocal`, `PT.e1aBetaCan_splitPlaces` and the proved localisation criterion);
* `himg` — the *unclaimed* direction of clause 2,

      extToIdeles y = 0 → ∃ c : ↥(Z2loc p k Ω K E), H2π (Z2ofZ2loc c) = e1aChainC p k Ω K … y,

  i.e. the `⟹` half of the chain--localisation comparison `(C')` of
  `ExtChain/NOTE_A1_A2_session_2026-10-01b.md` §2 (the per-place local degree-two dictionary in the
  direction `extLoc ⇒ chain`).  No file on disk produced it, which is why it is stated separately.

## Why these two suffice

* `PT.e1aBetaCan_eq_iff_chainC_mem_range` (proved) and `PT.sha2_range_iff` (proved) turn `hland`
  into the `⟸` half of `(C')`, and `himg` *is* its `⟹` half;
* `PT.e1aBetaCan_image_of_extToIdeles_iff` (proved) turns `(C')` into the image clause;
* `PT.e1a_ext_sha2_bridge_assembly` (proved) turns the image clause plus
  `PT.e1a_sha2_mem_range_chainC` into the node's statement, verbatim.

Nothing here is `sorry`-free yet only because `himg` is still open; this file is the record of the
wiring, not the finish.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/-- **`(C')` from its two halves.**  The `⟸` half is the landing clause in the `e1aBetaCan` form
(turned into the `Z2loc` form by the two proved range steps), the `⟹` half is `himg`. -/
theorem chainLocalisation_iff_of (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
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
    (hland : ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      (∃ b : Work.SSGRoute.Sha2 p k Ω K E,
          Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b = y) →
        SSGRoute.PTExt.extToIdeles (k := k) y = 0)
    (himg : ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      SSGRoute.PTExt.extToIdeles (k := k) y = 0 →
        ∃ c : ↥(Work.SSGRoute.Z2loc p k Ω K E),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            (Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E c) =
          Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      SSGRoute.PTExt.extToIdeles (k := k) y = 0 ↔
        ∃ c : ↥(Work.SSGRoute.Z2loc p k Ω K E),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            (Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E c) =
          Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y := by
  intro y
  refine ⟨himg y, fun hc => ?_⟩
  exact hland y
    ((Work.SSGRoute.PT.e1aBetaCan_eq_iff_chainC_mem_range p k Ω K ζ hζ hζK T hT E hmem y).mpr
      ((Work.SSGRoute.PT.sha2_range_iff p k Ω K E
        (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)).mpr hc))

/-- **The node, modulo its two interfaces.**

The conclusion is verbatim the statement of `Work.SSGRoute.ext_sha2_bridge`. -/
theorem ext_sha2_bridge_of (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (himg : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
        SSGRoute.PTExt.extToIdeles (k := k) y = 0 →
          ∃ c : ↥(Work.SSGRoute.Z2loc p k Ω K E),
            @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              (Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E c) =
            Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)
    (hland : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
          (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
            (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E).range),
        ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
          (∃ b : Work.SSGRoute.Sha2 p k Ω K E,
              Work.SSGRoute.PT.e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b = y) →
            SSGRoute.PTExt.extToIdeles (k := k) y = 0) :
    ∃ β : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Work.SSGRoute.Sha2 p k Ω K E →+
          CategoryTheory.Abelian.Ext
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
            (SSGRoute.PTExt.unitsK k K) 2,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E], Function.Injective (β E)) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (y : CategoryTheory.Abelian.Ext
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
            (SSGRoute.PTExt.unitsK k K) 2),
          (∃ b, β E b = y) ↔ SSGRoute.PTExt.extToIdeles y = 0) ∧
      ∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁]
        [DistribMulAction (K ≃ₐ[k] K) E₁] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (F : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
          SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
        (hF : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T) from F.hom φ)
            (TensorProduct.tmul (ZMod p) e t)
          = φ (TensorProduct.tmul (ZMod p) (f e) t))
        (b : Work.SSGRoute.Sha2 p k Ω K E₁),
        β E₂ (Work.SSGRoute.Sha2Map p k Ω K E₁ E₂ f hf b)
          = (CategoryTheory.Abelian.Ext.mk₀ F).comp (β E₁ b) (zero_add 2) :=
  Work.SSGRoute.PT.e1a_ext_sha2_bridge_assembly p k Ω K ζ hζ hζK T hT
    (fun (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] =>
      Work.SSGRoute.PT.e1a_sha2_mem_range_chainC p k Ω K ζ hζ hζK T hT E)
    (fun (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
          (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
            (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E).range) =>
      Work.SSGRoute.PT.e1aBetaCan_image_of_extToIdeles_iff p k Ω K ζ hζ hζK T hT E hmem
        (chainLocalisation_iff_of p k Ω K ζ hζ hζK T hT E hmem (hland E hmem) (himg E)))

end

end Work.SSGRoute.ExtChain
