import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.anchor_scale_close

/-!
# `Work.Pert.Ksub2.anchor_ball_tau0_norm_le`

The disc of radius `M / 40` around the datum's curve point `Xc d (-M) = τ₀ (φ₀ (-M))` is deep in
the left half plane: `anchor_scale_close` provides `‖Xc d (-M) + M‖ ≤ M / 40` for `M ≥ R₀`, so
every point `w` of the disc satisfies `‖w + M‖ < M / 20`, hence `‖w‖ > 19 M / 20 ≠ 0` and

`‖τ₀ w‖ = 1 / ‖w‖ < 20 / (19 M)`.

This is the "anchored ball stays off the pole `0` of `τ₀`" estimate used to compare the perturbed
coordinate with the datum's on that ball.
-/

namespace Work.Pert.Ksub2

open Complex Metric

/-- On the anchored ball `ball (Xc d (-M)) (M / 40)` (for `M` beyond a datum-dependent threshold)
the point `0` is avoided and `τ₀` is bounded by `20 / (19 M)`. -/
theorem anchor_ball_tau0_norm_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ M : ℝ, R ≤ M → ∀ w : ℂ,
      w ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) (M / 40) →
      w ≠ 0 ∧ ‖MandelDim.tau0 w‖ ≤ 20 / (19 * M) := by
  obtain ⟨R₀, _hR₀pos, hR₀⟩ := anchor_scale_close d
  refine ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun M hM w hw => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := le_trans (le_max_right _ _) hM
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hR : R₀ ≤ M := le_trans (le_max_left _ _) hM
  have hX := hR₀ M hR
  rw [Metric.mem_ball, dist_eq_norm] at hw
  set c : ℂ := Work.Pert.Xc d (((-M : ℝ)) : ℂ) with hc
  -- the disc is contained in the ball of radius `M/20` around `-M`
  have htri : ‖w - (((-M : ℝ)) : ℂ)‖ ≤ ‖w - c‖ + ‖c - (((-M : ℝ)) : ℂ)‖ := by
    have heq : w - (((-M : ℝ)) : ℂ) = (w - c) + (c - (((-M : ℝ)) : ℂ)) := by ring
    rw [heq]; exact norm_add_le _ _
  have hsmall : ‖w - (((-M : ℝ)) : ℂ)‖ < M / 20 := by
    have h2 : ‖c - (((-M : ℝ)) : ℂ)‖ ≤ M / 40 := hX
    linarith
  have hnormM : ‖(((-M : ℝ)) : ℂ)‖ = M := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact abs_of_pos hMpos
  have hrev : M ≤ ‖w‖ + ‖w - (((-M : ℝ)) : ℂ)‖ := by
    have h := norm_add_le ((((-M : ℝ)) : ℂ) - w) w
    rw [sub_add_cancel, hnormM, norm_sub_rev] at h
    linarith
  have hwbig : 19 * M / 20 ≤ ‖w‖ := by linarith
  have hwpos : 0 < ‖w‖ := by linarith
  have hne : w ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hwpos
    exact lt_irrefl 0 hwpos
  refine ⟨hne, ?_⟩
  have htau : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by simp [MandelDim.tau0]
  rw [htau]
  have hkey : 1 / ‖w‖ ≤ 1 / (19 * M / 20) := one_div_le_one_div_of_le (by linarith) hwbig
  have harith : 1 / (19 * M / 20) = 20 / (19 * M) := by rw [one_div, inv_div]
  rw [harith] at hkey
  exact hkey

end Work.Pert.Ksub2
