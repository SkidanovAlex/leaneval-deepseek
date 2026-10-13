import Mathlib

namespace Work.WilE9.Deriv

/-- If `φ : E →L[ℝ] F` is injective and `F` is finite-dimensional, then `g` is continuous on `s`
iff `φ ∘ g` is. (`F` finite-dimensional is needed only to make the linear left inverse of `φ`
continuous.)

Namespace `Work.WilE9.Deriv`; imports `Mathlib`; needs `open Topology`. -/
theorem continuousOn_iff_comp_injective
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : E →L[ℝ] F) (hφ : Function.Injective φ)
    {α : Type*} [TopologicalSpace α] (g : α → E) (s : Set α) :
    ContinuousOn (fun y => φ (g y)) s ↔ ContinuousOn g s := by
  -- An injective continuous linear map into a finite-dimensional space admits a
  -- continuous linear left inverse.
  have h : φ.HasLeftInverse :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hφ
  obtain ⟨ψ, hψ⟩ := h
  constructor
  · -- `g = ψ ∘ (φ ∘ g)`, and `ψ` is continuous.
    intro hcont
    have h1 : ContinuousOn (fun y => ψ (φ (g y))) s :=
      ψ.continuous.comp_continuousOn hcont
    rwa [show (fun y => ψ (φ (g y))) = g from funext fun y => hψ (g y)] at h1
  · -- `φ ∘ g` is a composite of continuous maps.
    intro hcont
    exact φ.continuous.comp_continuousOn hcont

end Work.WilE9.Deriv
