import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Finiteness

theorem exists_openSubgroup_factors_of_mem_lcCocycles
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (S : Finset (ValuationSubring Ω)) (f : (Ω ≃ₐ[k] Ω) → M)
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K M ⊤)
    (hunr : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → f σ = 0) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), U.FiniteIndex ∧ IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      (∀ g u : Ω ≃ₐ[k] Ω, u ∈ U → f (g * u) = f g) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → Work.SSGRoute.inertiaSub k Ω B ≤ U) ∧
      Subgroup.index U ≤ Nat.card M := by
  -- Unpack the hypotheses: `f` is a crossed-homomorphism 1-cocycle on all of `G_k`, locally
  -- constant for the Krull topology.
  obtain ⟨hcoc, hlc⟩ := (Work.SSGRoute.mem_lcCocycles p k Ω K M ⊤ f).mp hf
  -- The stabiliser of `f` under right translation: `U_f = {σ | ∀ τ, f (τ * σ) = f τ}`.
  let U : Subgroup (Ω ≃ₐ[k] Ω) :=
  { carrier := {σ | ∀ τ : Ω ≃ₐ[k] Ω, f (τ * σ) = f τ}
    one_mem' := by intro τ; rw [mul_one]
    mul_mem' := by
      intro σ ρ hσ hρ τ
      have h2 := hρ (τ * σ); rw [mul_assoc] at h2; rw [h2, hσ τ]
    inv_mem' := by
      intro σ hσ τ
      have h := hσ (τ * σ⁻¹); rw [mul_assoc, inv_mul_cancel, mul_one] at h; exact h.symm }
  have hU_mem : ∀ σ, σ ∈ U ↔ ∀ τ, f (τ * σ) = f τ := by intro σ; rfl
  -- The right translate `τ ↦ f (τ * σ)` is determined by `f σ`, so the orbit map factors through
  -- `f : G_k → M`; the resulting map `G_k ⧸ U → M` is injective.
  have hwd : ∀ a b : Ω ≃ₐ[k] Ω, (QuotientGroup.leftRel U) a b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have h := (hU_mem (a⁻¹ * b)).mp hab a
    rw [show a * (a⁻¹ * b) = b from by group] at h
    exact h.symm
  let Ψ : (Ω ≃ₐ[k] Ω) ⧸ U → M := fun q => Quotient.liftOn' q f hwd
  have hΨmk : ∀ a, Ψ ⟦a⟧ = f a := fun a => Quotient.liftOn'_mk a f hwd
  have hinj : Function.Injective Ψ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    rw [hΨmk a, hΨmk b] at hxy
    rw [Quotient.eq, QuotientGroup.leftRel_apply, hU_mem]
    intro τ
    have e1 : f τ = f (τ * a⁻¹) + SSGRoute.res k K (τ * a⁻¹) • f a := by
      have h := hcoc (τ * a⁻¹) (Subgroup.mem_top _) a (Subgroup.mem_top _)
      rw [mul_assoc, inv_mul_cancel, mul_one] at h; exact h
    have e2 : f (τ * (a⁻¹ * b)) = f (τ * a⁻¹) + SSGRoute.res k K (τ * a⁻¹) • f b := by
      have h := hcoc (τ * a⁻¹) (Subgroup.mem_top _) b (Subgroup.mem_top _)
      rw [mul_assoc] at h; exact h
    rw [e2, e1, hxy]
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · -- finite index, from the injection `G_k ⧸ U ↪ M` into the finite module `M`
    exact @Subgroup.finiteIndex_of_finite_quotient _ _ U (Finite.of_injective Ψ hinj)
  · -- openness: `IsLocConstOn ⊤ f` gives an open subgroup `V ⊆ U`
    obtain ⟨V, hVopen, hV⟩ := hlc
    exact Subgroup.isOpen_mono
      (fun u hu => (hU_mem u).mpr
        (fun τ => hV τ (Subgroup.mem_top τ) u hu (Subgroup.mem_top u))) hVopen
  · -- `f` is invariant under right translation by `U`
    intro g u hu
    exact (hU_mem u).mp hu g
  · -- `U` contains the inertia of every finite place not conjugate to an element of `S`
    intro B hB hconj σ hσ
    rw [Work.SSGRoute.mem_inertiaSub] at hσ
    rw [hU_mem]
    intro τ
    have h := hcoc τ (Subgroup.mem_top τ) σ (Subgroup.mem_top σ)
    rw [h, hunr B hB hconj σ hσ, smul_zero, add_zero]
  · -- the index bound, again from `G_k ⧸ U ↪ M`
    rw [Subgroup.index_eq_card]
    exact Nat.card_le_card_of_injective Ψ hinj

end Work.SSGRoute.Finiteness
