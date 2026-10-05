import Mathlib

namespace Work.RPB.B4

theorem partial_deriv_eq (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ 1 W) (τ t : ℝ) :
    HasDerivAt (fun s : ℝ => W (τ, s)) ((fderiv ℝ W (τ, t)) ((0:ℝ), 1)) t := by
  -- the curve s ↦ (τ, s) has derivative (0, 1) at t
  have hg : HasDerivAt (fun s : ℝ => (τ, s)) ((0:ℝ), 1) t := by
    simpa using (hasDerivAt_const t τ).prodMk (hasDerivAt_id t)
  -- W is differentiable at (τ, t) with derivative fderiv ℝ W (τ, t)
  have hW' : HasFDerivAt W (fderiv ℝ W (τ, t)) (τ, t) :=
    (hW.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  -- chain rule: (W ∘ (s ↦ (τ, s)))' = fderiv ℝ W (τ,t) applied to (0,1)
  exact hW'.comp_hasDerivAt t hg

end Work.RPB.B4
