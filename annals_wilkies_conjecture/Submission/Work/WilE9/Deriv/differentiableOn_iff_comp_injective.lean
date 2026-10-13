import Mathlib

namespace Work.WilE9.Deriv

/-- An injective continuous linear map `φ : E →L[ℝ] F` into a finite-dimensional space `F`
admits a continuous linear left inverse `ψ : F →L[ℝ] E`.

A linear left inverse `σ` exists because `φ` is injective, and it is automatically continuous
because its domain `F` is finite-dimensional. -/
theorem exists_leftInverse_clm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : E →L[ℝ] F) (hφ : Function.Injective φ) :
    ∃ ψ : F →L[ℝ] E, ∀ e, ψ (φ e) = e := by
  have hker : φ.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hφ
  obtain ⟨σ, hσ⟩ := LinearMap.exists_leftInverse_of_injective φ.toLinearMap hker
  refine ⟨LinearMap.toContinuousLinearMap σ, ?_⟩
  intro e
  have h := congrArg (fun (f : E →ₗ[ℝ] E) => f e) hσ
  simpa [LinearMap.comp_apply] using h

/-- If `φ : E →L[ℝ] F` is injective and `F` is finite-dimensional, then `g` is differentiable on
`s` iff `φ ∘ g` is.

Namespace `Work.WilE9.Deriv`; imports `Mathlib`. -/
theorem differentiableOn_iff_comp_injective
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : E →L[ℝ] F) (hφ : Function.Injective φ)
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] (g : α → E) (s : Set α) :
    DifferentiableOn ℝ (fun y => φ (g y)) s ↔ DifferentiableOn ℝ g s := by
  obtain ⟨ψ, hψ⟩ := exists_leftInverse_clm φ hφ
  constructor
  · intro hu
    have hcomp : DifferentiableOn ℝ (ψ ∘ (fun y => φ (g y))) s :=
      (ψ.differentiableOn).comp hu (Set.mapsTo_image (fun y => φ (g y)) s)
    have heq : (ψ ∘ (fun y => φ (g y))) = g := by
      funext y; exact hψ (g y)
    rw [heq] at hcomp
    exact hcomp
  · intro hg
    exact (φ.differentiableOn).comp hg (Set.mapsTo_image g s)

end Work.WilE9.Deriv
