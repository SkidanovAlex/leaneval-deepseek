import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

theorem factorCocycle_of_vanishingOn_ker (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    {M : Type} [AddCommGroup M] [DistribMulAction (K ≃ₐ[k] K) M]
    (φ : (Ω ≃ₐ[k] Ω) → M) (hφ : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ φ)
    (hker : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ K.fixingSubgroup → φ σ = 0) :
    ∃ ψ : (K ≃ₐ[k] K) → M,
      SSGRoute.IsCocycleOn (MonoidHom.id (K ≃ₐ[k] K)) ⊤ ψ ∧ φ = ψ ∘ (SSGRoute.res k K) := by
  -- The restriction map is surjective (every `k`-embedding of the normal extension `K`
  -- extends to the algebraic closure `Ω`).
  have hsurj : Function.Surjective (SSGRoute.res k K) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  have hspec : ∀ τ : K ≃ₐ[k] K, SSGRoute.res k K (Function.surjInv hsurj τ) = τ :=
    fun τ => Function.surjInv_eq hsurj τ
  -- Vanishing on `ker res = K.fixingSubgroup` makes `φ` constant on the fibres of `res`,
  -- so it descends to a well defined function on `Gal(K/k)`.
  have hwd : ∀ σ σ' : Ω ≃ₐ[k] Ω, SSGRoute.res k K σ = SSGRoute.res k K σ' → φ σ = φ σ' := by
    intro σ σ' h
    have h1 : SSGRoute.res k K (σ⁻¹ * σ') = 1 := by
      simp only [map_mul, map_inv, h, inv_mul_cancel]
    have hmem : σ⁻¹ * σ' ∈ K.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker K]
      exact MonoidHom.mem_ker.mpr h1
    have hφ0 : φ (σ⁻¹ * σ') = 0 := hker _ hmem
    have h2 := hφ σ (Subgroup.mem_top σ) (σ⁻¹ * σ') (Subgroup.mem_top _)
    rw [hφ0, smul_zero, add_zero] at h2
    have hmul : σ * (σ⁻¹ * σ') = σ' := by group
    rw [hmul] at h2
    exact h2.symm
  refine ⟨fun τ => φ (Function.surjInv hsurj τ), ?_, ?_⟩
  · intro g _ h _
    have key : φ (Function.surjInv hsurj (g * h))
        = φ (Function.surjInv hsurj g * Function.surjInv hsurj h) :=
      hwd _ _ (by simp only [map_mul, hspec])
    have hc := hφ (Function.surjInv hsurj g) (Subgroup.mem_top _)
      (Function.surjInv hsurj h) (Subgroup.mem_top _)
    rw [hspec g] at hc
    show φ (Function.surjInv hsurj (g * h)) = φ (Function.surjInv hsurj g) + g • φ (Function.surjInv hsurj h)
    rw [key, hc]
  · funext σ
    exact hwd σ (Function.surjInv hsurj (SSGRoute.res k K σ)) (hspec _).symm

end Work.SSGRoute
