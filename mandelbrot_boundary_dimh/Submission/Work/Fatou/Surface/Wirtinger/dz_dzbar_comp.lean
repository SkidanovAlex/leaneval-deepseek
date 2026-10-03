import Mathlib
import Submission.Work.Interfaces.Fatou

namespace Work.Fatou.Surface.Wirtinger

/-- The Wirtinger chain rule when the outer function is complex differentiable (holomorphic):
`∂(f ∘ h) = f'(h z) · ∂h` and `∂̄(f ∘ h) = f'(h z) · ∂̄h`. -/
theorem dz_dzbar_comp {f h : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f (h z))
    (hh : DifferentiableAt ℝ h z) :
    MandelDim.dz (f ∘ h) z = deriv f (h z) * MandelDim.dz h z ∧
      MandelDim.dzbar (f ∘ h) z = deriv f (h z) * MandelDim.dzbar h z := by
  -- `f` is complex differentiable at `h z`, hence real differentiable there with
  -- real (Fréchet) derivative the real-linear map `w ↦ deriv f (h z) * w`.
  have hfd : fderiv ℝ (f ∘ h) z =
      ((deriv f (h z)) • (1 : ℂ →L[ℝ] ℂ)) ∘SL (fderiv ℝ h z) :=
    ((hf.hasDerivAt.complexToReal_fderiv).comp z hh.hasFDerivAt).fderiv
  constructor <;> simp only [MandelDim.dz, MandelDim.dzbar]
  · rw [hfd]
    simp only [ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self]
    ring
  · rw [hfd]
    simp only [ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self]
    ring

end Work.Fatou.Surface.Wirtinger
