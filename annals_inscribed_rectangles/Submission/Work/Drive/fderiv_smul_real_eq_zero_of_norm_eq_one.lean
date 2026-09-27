import Mathlib

namespace Work.Drive

/-- If `U : E → ℂ` takes values in the unit circle and is real-differentiable at `x`, then the
differential of `U` at `x` cannot be a non-zero real multiple of the value `U x`: a map into the
unit sphere has tangential derivative. -/
theorem fderiv_smul_real_eq_zero_of_norm_eq_one {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : E → ℂ} {x w : E} {l : ℝ}
    (hU : ∀ y, ‖U y‖ = 1) (hd : DifferentiableAt ℝ U x)
    (h : fderiv ℝ U x w = l • U x) : l = 0 := by
  -- `‖U ·‖ ^ 2` is the constant function `1`, so its derivative vanishes.
  have hconst : (fun y : E => ‖U y‖ ^ 2) = fun _ => (1 : ℝ) := by
    funext y; rw [hU y]; norm_num
  have hzero : fderiv ℝ (fun y : E => ‖U y‖ ^ 2) x w = 0 := by
    rw [hconst]; simp
  -- Rewrite `‖U ·‖ ^ 2` as the real inner product `⟪U ·, U ·⟫` and apply the product rule.
  have hfun : (fun t : E => inner ℝ (U t) (U t)) = fun t => ‖U t‖ ^ 2 :=
    funext fun t => real_inner_self_eq_norm_sq (U t)
  have hinner := fderiv_inner_apply (𝕜 := ℝ) (f := U) (g := U) hd hd w
  rw [hfun] at hinner
  have h2 : inner ℝ (U x) (fderiv ℝ U x w) + inner ℝ (fderiv ℝ U x w) (U x) = 0 := by
    rw [← hinner]; exact hzero
  -- Substitute the hypothesis and evaluate.
  rw [h] at h2
  rw [real_inner_smul_right, real_inner_smul_left, real_inner_self_eq_norm_sq, hU x] at h2
  norm_num at h2
  linarith

end Work.Drive
