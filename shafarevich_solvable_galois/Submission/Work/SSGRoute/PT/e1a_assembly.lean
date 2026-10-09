import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: assembly of the target theorem from the canonical `β`

This module assembles the target `Work.SSGRoute.PT.e1a_ext_sha2_bridge` from

* the canonical map `PT.e1aBetaCan` (with its injectivity `PT.e1aBetaCan_injective`, its computation
  rule `PT.e1aBetaCan_chainC` and its naturality `PT.e1aBetaCan_natural`), which needs the *membership
  clause* `hmem` as an input, and
* the two arithmetic inputs, taken here as **hypotheses** (so that this file is independent of their
  provers):
  - `hcr` : the crux — the canonical chain `e1aChainC` hits the class of every locally trivial
    `2`-cocycle (supplied on disk by `SSGRoute/PT/e1a_sha2_mem_range_chainC`);
  - `himg` : the image clause — `range β = ker extToIdeles` (supplied on disk by
    `SSGRoute/PT/e1aBetaCan_image`).

The file proves `Work.SSGRoute.PT.e1a_ext_sha2_bridge_assembly`, whose conclusion is *exactly* the
statement of the target theorem, so that the target file is a one-line application.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-- **The membership clause of the canonical chain**, from the crux `hcr`: the canonical bridge
`φ = Classical.choose (sha2_to_H2AK …)` lands in the range of `e1aChainC`. -/
theorem e1aChainC_mem_range (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (hcr : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
      (hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
        @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
          (DistribMulAction.compHom E (SSGRoute.res k K))),
      c ∈ Work.SSGRoute.Z2loc p k Ω K E →
      ∃ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
        e1aChainC p k Ω K ζ hζ hζK T hT E y =
          (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩)) :
    ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
      (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
        (e1aChainC p k Ω K ζ hζ hζK T hT E).range := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  intro b
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
  exact hcr c.1 hZ c.2

/-- The canonical family `β`, from the crux `hcr`. -/
noncomputable def e1aBetaFamily (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hcr : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
        (hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
          @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))),
        c ∈ Work.SSGRoute.Z2loc p k Ω K E →
        ∃ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
          e1aChainC p k Ω K ζ hζ hζK T hT E y =
            (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩))
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Work.SSGRoute.Sha2 p k Ω K E →+
      CategoryTheory.Abelian.Ext
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
        (SSGRoute.PTExt.unitsK k K) 2 :=
  e1aBetaCan p k Ω K ζ hζ hζK T hT E (e1aChainC_mem_range p k Ω K ζ hζ hζK T hT E (hcr E))

/-- Injectivity of the canonical family `β` (clause (1) of the target). -/
theorem e1aBetaFamily_injective (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hcr : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
        (hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
          @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))),
        c ∈ Work.SSGRoute.Z2loc p k Ω K E →
        ∃ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
          e1aChainC p k Ω K ζ hζ hζK T hT E y =
            (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩))
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Function.Injective (e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E) := by
  unfold e1aBetaFamily
  exact e1aBetaCan_injective p k Ω K ζ hζ hζK T hT E _

/-- The image clause of the canonical family `β` (clause (2) of the target), from the arithmetic
input `himg`. -/
theorem e1aBetaFamily_image (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hcr : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
        (hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
          @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))),
        c ∈ Work.SSGRoute.Z2loc p k Ω K E →
        ∃ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
          e1aChainC p k Ω K ζ hζ hζK T hT E y =
            (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩))
    (himg : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
          (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
            (e1aChainC p k Ω K ζ hζ hζK T hT E).range),
        ∀ y : CategoryTheory.Abelian.Ext
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
            (SSGRoute.PTExt.unitsK k K) 2,
          (∃ b, e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b = y) ↔
            SSGRoute.PTExt.extToIdeles y = 0)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ∀ y : CategoryTheory.Abelian.Ext
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
        (SSGRoute.PTExt.unitsK k K) 2,
      (∃ b, e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E b = y) ↔
        SSGRoute.PTExt.extToIdeles y = 0 := by
  intro y
  unfold e1aBetaFamily
  exact himg E _ y

/-- Naturality of the canonical family `β` (clause (3) of the target). -/
theorem e1aBetaFamily_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hcr : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
        (hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
          @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))),
        c ∈ Work.SSGRoute.Z2loc p k Ω K E →
        ∃ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
          e1aChainC p k Ω K ζ hζ hζK T hT E y =
            (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩))
    (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
    (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
    (F : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
        SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
    (hF : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
      (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T) from F.hom φ)
        (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (b : Work.SSGRoute.Sha2 p k Ω K E₁) :
    e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E₂
        (Work.SSGRoute.Sha2Map p k Ω K E₁ E₂ f hf b) =
      (CategoryTheory.Abelian.Ext.mk₀ F).comp
        (e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E₁ b) (zero_add 2) := by
  unfold e1aBetaFamily
  exact e1aBetaCan_natural p k Ω K ζ hζ hζK T hT E₁ E₂ f hf F hF _ _ b

/-- **Assembly of the target theorem** from the two arithmetic inputs (the crux `hcr` and the image
clause `himg`); the conclusion is *exactly* the statement of
`Work.SSGRoute.PT.e1a_ext_sha2_bridge`. -/
theorem e1a_ext_sha2_bridge_assembly (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hcr : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
        (hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
          @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))),
        c ∈ Work.SSGRoute.Z2loc p k Ω K E →
        ∃ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
          e1aChainC p k Ω K ζ hζ hζK T hT E y =
            (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩))
    (himg : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
          (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
            (e1aChainC p k Ω K ζ hζ hζK T hT E).range),
        ∀ y : CategoryTheory.Abelian.Ext
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
            (SSGRoute.PTExt.unitsK k K) 2,
          (∃ b, e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b = y) ↔
            SSGRoute.PTExt.extToIdeles y = 0) :
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
          = (CategoryTheory.Abelian.Ext.mk₀ F).comp (β E₁ b) (zero_add 2) := by
  refine ⟨e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr, ?_, ?_, ?_⟩
  · intro E _ _ _ _ _ a₁ a₂ h
    exact e1aBetaFamily_injective p k Ω K ζ hζ hζK T hT hcr E h
  · intro E _ _ _ _ _ y
    exact e1aBetaFamily_image p k Ω K ζ hζ hζK T hT hcr himg E y
  · intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf F hF b
    exact e1aBetaFamily_natural p k Ω K ζ hζ hζK T hT hcr E₁ E₂ f hf F hF b

end

end Work.SSGRoute.PT
