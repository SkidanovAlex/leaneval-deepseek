import Mathlib
import Submission.Work.SSGRoute.PT.e1a_can_chain
import Submission.Work.SSGRoute.PT.sha2ToH2AK_chosen_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: the *canonical* assembled map `β : Ш²(k,E) → Ext²_{Gal(K/k)}(E',Kˣ)`

This module assembles `β` from the canonical chain `PT.e1aChainC` and the canonical
`Sha2 → H²(Γ,E)` bridge `Classical.choose (PT.sha2_to_H2AK …)`:

`Ш²(k,E) --φ--> H²(Γ,E) --(codRestrict to `range (e1aChainC E)`)--> range (e1aChainC E)`
`  --(inverse of the range isomorphism)--> Ext²_G(E',Kˣ)`.

Because `e1aChainC` is injective, on its range it is an isomorphism onto its range, so `β` is
*additive by construction* and its defining property is the computation rule
`e1aChainC (β b) = φ b`.  Well-definedness therefore only needs the membership clause

`hmem : ∀ b, φ b ∈ (e1aChainC E).range`

(the arithmetic crux, delegated as `SSGRoute/PT/e1a_sha2_mem_range_chainC`) — and it is the *only*
arity input of this file: everything else (injectivity of `β`, and the naturality of `β` in `E`,
which is clause (3) of the target) is proved here from the naturality of the chain
(`PT.e1aChainC_natural`) and of the bridge (`PT.sha2ToH2AK_chosen_natural`).
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

attribute [local instance] Work.SSGRoute.freeCoverSES_finite

/-- The canonical chain of the coefficient `E` is injective on its range; this is the
*range isomorphism* used to invert it. -/
noncomputable def e1aChainRangeEquiv (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2 ≃+
      (e1aChainC p k Ω K ζ hζ hζK T hT E).range := by
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hN : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  exact AddEquiv.ofBijective
    ((e1aChainC p k Ω K ζ hζ hζK T hT E).codRestrict
      (e1aChainC p k Ω K ζ hζ hζK T hT E).range
      (fun y => AddMonoidHom.mem_range.mpr ⟨y, rfl⟩))
    ⟨fun x y hxy => e1aChainC_injective p k Ω K ζ hζ hζK T hT E (Subtype.ext_iff.mp hxy),
      fun y => ⟨Classical.choose (AddMonoidHom.mem_range.mp y.2),
        Subtype.ext (by
          show (e1aChainC p k Ω K ζ hζ hζK T hT E)
            (Classical.choose (AddMonoidHom.mem_range.mp y.2)) = ↑y
          exact Classical.choose_spec (AddMonoidHom.mem_range.mp y.2))⟩⟩

/-- Computation rule of the range isomorphism: its coercion is the chain. -/
theorem e1aChainRangeEquiv_apply (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (x : Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2) :
    ((e1aChainRangeEquiv p k Ω K ζ hζ hζK T hT E x : (e1aChainC p k Ω K ζ hζ hζK T hT E).range) :
        @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) E _ _ _
          (DistribMulAction.compHom E (SSGRoute.res k K))) =
      e1aChainC p k Ω K ζ hζ hζK T hT E x := rfl

/-- **The assembled canonical map** `β : Ш²(k,E) → Ext²_{Gal(K/k)}(E',Kˣ)`, from the membership
clause `hmem` (the arithmetic crux) and the canonical bridge `φ = Classical.choose
(sha2_to_H2AK …)`. -/
noncomputable def e1aBetaCan (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
      (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
        (e1aChainC p k Ω K ζ hζ hζK T hT E).range) :
    Work.SSGRoute.Sha2 p k Ω K E →+
      Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2 :=
  (e1aChainRangeEquiv p k Ω K ζ hζ hζK T hT E).symm.toAddMonoidHom.comp
    ((Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)).codRestrict
      (e1aChainC p k Ω K ζ hζ hζK T hT E).range hmem)

/-- **The computation rule of `β`**: `e1aChainC (β b) = φ b`. -/
theorem e1aBetaCan_chainC (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
      (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
        (e1aChainC p k Ω K ζ hζ hζK T hT E).range)
    (b : Work.SSGRoute.Sha2 p k Ω K E) :
    e1aChainC p k Ω K ζ hζ hζK T hT E (e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b) =
      (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b := by
  change (e1aChainC p k Ω K ζ hζ hζK T hT E)
      ((e1aChainRangeEquiv p k Ω K ζ hζ hζK T hT E).symm
        (((Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)).codRestrict
          (e1aChainC p k Ω K ζ hζ hζK T hT E).range hmem) b)) =
    (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b
  rw [← e1aChainRangeEquiv_apply p k Ω K ζ hζ hζK T hT E
    ((e1aChainRangeEquiv p k Ω K ζ hζ hζK T hT E).symm
      (((Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)).codRestrict
        (e1aChainC p k Ω K ζ hζ hζK T hT E).range hmem) b))]
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- **Injectivity of `β`** (it is the composite of an isomorphism with the (injective) bridge). -/
theorem e1aBetaCan_injective (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
      (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
        (e1aChainC p k Ω K ζ hζ hζK T hT E).range) :
    Function.Injective (e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem) := by
  intro b b' hbb'
  have h1 : e1aChainC p k Ω K ζ hζ hζK T hT E
      (e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b) =
      e1aChainC p k Ω K ζ hζ hζK T hT E
      (e1aBetaCan p k Ω K ζ hζ hζK T hT E hmem b') := by rw [hbb']
  rw [e1aBetaCan_chainC p k Ω K ζ hζ hζK T hT E hmem b,
    e1aBetaCan_chainC p k Ω K ζ hζ hζK T hT E hmem b'] at h1
  exact (Classical.choose_spec (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)).1 h1

/-- **Naturality of `β` in the coefficient `E`** (clause (3) of the target theorem), from the
naturality of the chain (`PT.e1aChainC_natural`), of the bridge
(`PT.sha2ToH2AK_chosen_natural`) and the computation rule. -/
theorem e1aBetaCan_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
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
    (hmem₁ : ∀ b : Work.SSGRoute.Sha2 p k Ω K E₁,
      (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E₁)) b ∈
        (e1aChainC p k Ω K ζ hζ hζK T hT E₁).range)
    (hmem₂ : ∀ b : Work.SSGRoute.Sha2 p k Ω K E₂,
      (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E₂)) b ∈
        (e1aChainC p k Ω K ζ hζ hζK T hT E₂).range)
    (b : Work.SSGRoute.Sha2 p k Ω K E₁) :
    e1aBetaCan p k Ω K ζ hζ hζK T hT E₂ hmem₂
        (Work.SSGRoute.Sha2Map p k Ω K E₁ E₂ f hf b) =
      (Abelian.Ext.mk₀ F).comp (e1aBetaCan p k Ω K ζ hζ hζK T hT E₁ hmem₁ b)
        (zero_add 2) := by
  apply e1aChainC_injective p k Ω K ζ hζ hζK T hT E₂
  rw [e1aBetaCan_chainC p k Ω K ζ hζ hζK T hT E₂ hmem₂
      (Work.SSGRoute.Sha2Map p k Ω K E₁ E₂ f hf b),
    Work.SSGRoute.PT.sha2ToH2AK_chosen_natural p k Ω K E₁ E₂ f hf b,
    e1aChainC_natural p k Ω K ζ hζ hζK T hT E₁ E₂ f hf F hF
      (e1aBetaCan p k Ω K ζ hζ hζK T hT E₁ hmem₁ b),
    e1aBetaCan_chainC p k Ω K ζ hζ hζK T hT E₁ hmem₁ b]

end

end Work.SSGRoute.PT
