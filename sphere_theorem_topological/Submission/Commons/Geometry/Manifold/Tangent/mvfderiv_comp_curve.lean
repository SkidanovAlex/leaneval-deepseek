import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace Commons.Geometry.Manifold.Tangent

open scoped _root_.Manifold _root_.ContDiff

/-- **The chain rule along a curve.**  For `g : M → F` differentiable at `γ t` and `γ`
differentiable at `t`, the directional derivative of `g` at `γ t` in the direction of the velocity
of `γ` is the ordinary derivative of the composite `g ∘ γ`. -/
theorem mvfderiv_comp_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : M → F} {γ : ℝ → M} {t : ℝ}
    (hg : MDifferentiableAt I 𝓘(ℝ, F) g (γ t)) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    mvfderiv I g (γ t) (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)) = deriv (g ∘ γ) t := by
  have h1 : mfderiv 𝓘(ℝ) 𝓘(ℝ, F) (g ∘ γ) t (1 : ℝ)
      = mfderiv I 𝓘(ℝ, F) g (γ t) (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)) :=
    mfderiv_comp_apply (x := t) hg hγ (1 : ℝ)
  rw [mvfderiv, ContinuousLinearMap.comp_apply]
  rw [← h1, mfderiv_eq_fderiv]
  rfl

end Commons.Geometry.Manifold.Tangent