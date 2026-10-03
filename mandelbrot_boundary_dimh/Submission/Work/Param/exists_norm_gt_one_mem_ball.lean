import Mathlib

namespace Work.Param

/-- Points of the unit circle can be approximated by points of strictly larger norm:
for `‖l‖ = 1` and `δ > 0` the point `(1 + δ/2) • l` lies in the open ball of radius `δ`
about `l` and has norm `1 + δ/2 > 1`. -/
theorem exists_norm_gt_one_mem_ball {l : ℂ} (hl : ‖l‖ = 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℂ, 1 < ‖t‖ ∧ t ∈ Metric.ball l δ := by
  refine ⟨((1 + δ / 2 : ℝ) : ℂ) * l, ?_, ?_⟩
  · rw [norm_mul, hl, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < 1 + δ / 2)]
    linarith
  · rw [Metric.mem_ball, dist_eq_norm]
    have h : ((1 + δ / 2 : ℝ) : ℂ) * l - l = ((δ / 2 : ℝ) : ℂ) * l := by
      push_cast; ring
    rw [h, norm_mul, hl, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < δ / 2)]
    linarith

end Work.Param
