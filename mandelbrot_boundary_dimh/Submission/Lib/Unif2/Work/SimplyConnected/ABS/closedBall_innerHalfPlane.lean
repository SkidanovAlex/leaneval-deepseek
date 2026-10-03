import Mathlib

namespace Work.SimplyConnected.ABS

/-- **A round ball lies on the inner side of its boundary tangent lines.**  For a closed ball
`Metric.closedBall c ρ` with `ρ > 0` and a boundary point `p` (`‖p - c‖ = ρ`), the outward unit
normal `u = ρ⁻¹ • (p - c)` satisfies `inner ℝ u (w - p) ≤ 0` for every `w` of the ball. -/
theorem closedBall_innerHalfPlane (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {p : ℂ} (hp : ‖p - c‖ = ρ) :
    ‖((ρ⁻¹ : ℝ) : ℂ) * (p - c)‖ = 1 ∧
      ∀ w ∈ Metric.closedBall c ρ, inner ℝ (((ρ⁻¹ : ℝ) : ℂ) * (p - c)) (w - p) ≤ 0 := by
  have hnorm : ‖((ρ⁻¹ : ℝ) : ℂ) * (p - c)‖ = 1 := by
    rw [← Complex.real_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), hp,
      inv_mul_cancel₀ (ne_of_gt hρ)]
  refine ⟨hnorm, ?_⟩
  intro w hw
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  -- `inner ℝ (p - c) (p - c) = ρ ^ 2`
  have hself : inner ℝ (p - c) (p - c) = ρ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, hp]
  -- the boundary point `p` sits exactly on the normal line `inner ℝ u · = ρ`
  have h1 : inner ℝ (((ρ⁻¹ : ℝ) : ℂ) * (p - c)) (p - c) = ρ := by
    rw [← Complex.real_smul, inner_smul_left, starRingEnd_apply, star_trivial, hself, sq,
      inv_mul_cancel_left₀ (ne_of_gt hρ)]
  -- Cauchy–Schwarz bounds `inner ℝ u ·` on the ball by `ρ`
  have h2 : inner ℝ (((ρ⁻¹ : ℝ) : ℂ) * (p - c)) (w - c) ≤ ρ := by
    calc inner ℝ (((ρ⁻¹ : ℝ) : ℂ) * (p - c)) (w - c)
        ≤ ‖((ρ⁻¹ : ℝ) : ℂ) * (p - c)‖ * ‖w - c‖ := real_inner_le_norm _ _
      _ = 1 * ‖w - c‖ := by rw [hnorm]
      _ ≤ ρ := by rw [one_mul]; exact hw
  have h3 : w - p = (w - c) - (p - c) := by ring
  rw [h3, inner_sub_right, h1]
  linarith

end Work.SimplyConnected.ABS
