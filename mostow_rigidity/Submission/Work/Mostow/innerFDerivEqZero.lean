import Mathlib

namespace Work.Mostow

/-- If `f : E → E` is `C¹` on an open set `U` and `‖f x‖ = 1` for all `x ∈ U`,
then the derivative of `f` at any `x ∈ U` is perpendicular to `f x`. -/
theorem innerFDerivEqZero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → E) (hf : ContDiff ℝ 1 f) {U : Set E} (hU : IsOpen U)
    (h : ∀ x ∈ U, ‖f x‖ = 1) :
    ∀ x ∈ U, ∀ v : E, inner ℝ (fderiv ℝ f x v) (f x) = 0 := by
  intro x hx v
  have hdf : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)).differentiableAt
  -- `t ↦ ⟪f t, f t⟫` is constantly `1` near `x`
  have hg : (fun t => inner ℝ (f t) (f t)) =ᶠ[nhds x] Function.const E (1:ℝ) := by
    filter_upwards [hU.mem_nhds hx] with t ht
    rw [real_inner_self_eq_norm_sq, h t ht]
    norm_num
  have hzero : fderiv ℝ (fun t => inner ℝ (f t) (f t)) x = 0 := by
    rw [hg.fderiv_eq]
    simp
  have h0 : fderiv ℝ (fun t => inner ℝ (f t) (f t)) x v = 0 := by rw [hzero]; rfl
  have hkey := fderiv_inner_apply (𝕜 := ℝ) hdf hdf v
  rw [h0] at hkey
  rw [real_inner_comm ((fderiv ℝ f x) v) (f x)] at hkey
  linarith

end Work.Mostow
