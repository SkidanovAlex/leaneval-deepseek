import Mathlib

namespace Work.OddVolterra.KernelExt

open scoped Topology

/-- The directional derivative of `F : ℝ × ℝ × ℝ → ℝ` at `(s, σ, t)` in the direction
of the first coordinate equals the one-variable derivative of `u ↦ F (u, σ, t)` at `s`. -/
theorem fderiv_fst_eq_deriv (F : ℝ × ℝ × ℝ → ℝ) (s σ t : ℝ)
    (hF : DifferentiableAt ℝ F (s, σ, t)) :
    (fderiv ℝ F (s, σ, t)) (1, 0, 0) = deriv (fun u : ℝ => F (u, σ, t)) s := by
  -- The curve `u ↦ (u, σ, t)` is affine, with derivative `u ↦ (u, 0, 0)`.
  have hg : HasFDerivAt (fun u : ℝ => (u, σ, t))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ × ℝ)) s := by
    have h := (hasFDerivAt_id (𝕜 := ℝ) s).prodMk (hasFDerivAt_const (𝕜 := ℝ) (σ, t) s)
    simpa using h
  -- Chain rule along that curve.
  have hcomp : HasFDerivAt (fun u : ℝ => F (u, σ, t))
      ((fderiv ℝ F (s, σ, t)) ∘SL ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ × ℝ))) s := by
    simpa [Function.comp_def] using (hF.hasFDerivAt).comp s hg
  rw [← fderiv_apply_one_eq_deriv, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rfl

end Work.OddVolterra.KernelExt
