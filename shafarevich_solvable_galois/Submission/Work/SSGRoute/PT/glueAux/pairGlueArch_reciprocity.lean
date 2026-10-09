import Mathlib
import Submission.Work.SSGRoute.PT.glueOfTwoHalvesDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped TensorProduct BigOperators

set_option linter.unusedVariables false

namespace Work.SSGRoute.PT

theorem pairGlueArch_reciprocity
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (fin : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
        ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (arch : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
        ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hrecJoint : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
        (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
          ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
        ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
        (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
        (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
        ∑ A ∈ S', fin M (SSGRoute.decomp k A) a b +
          ∑ c ∈ C', arch M (Subgroup.zpowers c) a b = 0)
    (hempty : E7Arch.LocalGroupDisjoint k Ω) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      H1Pair.PairReciprocity p K T M
        (fun H a b => pairGlueArch p k Ω K ζ hζ hζK T hT fin arch M H a b) := by
  intro M _ _ _ _ _ a b ha1 ha2 hb1 hb2 S' hS'fin hS'disj hS'unram C' hC'inv hC'rep hC'disj
  have h1 : ∑ A ∈ S', pairGlueArch p k Ω K ζ hζ hζK T hT fin arch M (SSGRoute.decomp k A) a b
      = ∑ A ∈ S', fin M (SSGRoute.decomp k A) a b := by
    refine Finset.sum_congr rfl fun A hA => ?_
    exact pairGlueArch_decomp p k Ω K ζ hζ hζK T hT fin arch hempty M A (hS'fin A hA) a b
  have h2 : ∑ c ∈ C', pairGlueArch p k Ω K ζ hζ hζK T hT fin arch M (Subgroup.zpowers c) a b
      = ∑ c ∈ C', arch M (Subgroup.zpowers c) a b := by
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [pairGlueArch_arch p k Ω K ζ hζ hζK T hT fin arch M (hC'inv c hc) rfl a b]
  rw [h1, h2]
  exact hrecJoint M a b ha1 ha2 hb1 hb2 S' hS'fin hS'disj hS'unram C' hC'inv hC'rep hC'disj


end Work.SSGRoute.PT
