import Mathlib
import Submission.Work.RPB.B1a.HalfBallRegion

set_option linter.unusedVariables false

namespace Work.RPB.B1a

theorem shearRegion_horiz_mem (P Q : ℝ → ℝ) {r x y z : ℝ} (hr : 0 < r)
    (hmono : ∀ y ∈ Set.Ioo 0 r,
      MonotoneOn (fun x => (y - P x) ^ 2 + (Q x) ^ 2) (Set.Icc 0 (2 * r)) ∧
      AntitoneOn (fun x => (y - P x) ^ 2 + (Q x) ^ 2) (Set.Icc (-2 * r) 0))
    (h : (x, y) ∈ Work.RPB.B1a.shearRegion P Q r) (hyr : y < r) (hz : z ∈ Set.uIcc 0 x) :
    (z, y) ∈ Work.RPB.B1a.shearRegion P Q r := by
  rw [mem_shearRegion] at h ⊢
  obtain ⟨hy0, hfx, hball⟩ := h
  -- the ball membership controls `|x|` and `|y|`
  have hball' : ‖(x, y)‖ < 2 * r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hball
  have hx_abs : |x| < 2 * r := by
    have := norm_fst_le (x, y); rw [Real.norm_eq_abs] at this; linarith
  have hy_abs : |y| < 2 * r := by
    have := norm_snd_le (x, y); rw [Real.norm_eq_abs] at this; linarith
  have hx_lt : x < 2 * r := (abs_lt.mp hx_abs).2
  have hx_gt : -(2 * r) < x := (abs_lt.mp hx_abs).1
  have hzu : 0 ≤ z ∧ z ≤ x ∨ x ≤ z ∧ z ≤ 0 := Set.mem_uIcc.mp hz
  have hz_abs : |z| < 2 * r := by
    rcases hzu with ⟨hz0, hzx⟩ | ⟨hzx, hz0⟩
    · rw [abs_of_nonneg hz0]; linarith
    · rw [abs_of_nonpos hz0]; linarith
  refine ⟨hy0, ?_, ?_⟩
  · -- the value of `(y - P ·)^2 + (Q ·)^2` at `z` is at most its value at `x`
    have hyn : y ∈ Set.Ioo 0 r := ⟨hy0, hyr⟩
    obtain ⟨hmono1, hmono2⟩ := hmono y hyn
    rcases hzu with ⟨hz0, hzx⟩ | ⟨hzx, hz0⟩
    · have hzi : z ∈ Set.Icc 0 (2 * r) := ⟨hz0, by linarith⟩
      have hxi : x ∈ Set.Icc 0 (2 * r) := ⟨le_trans hz0 hzx, hx_lt.le⟩
      exact lt_of_le_of_lt (hmono1 hzi hxi hzx) hfx
    · have hzi : z ∈ Set.Icc (-2 * r) 0 := ⟨by linarith, hz0⟩
      have hxi : x ∈ Set.Icc (-2 * r) 0 := ⟨by linarith, by linarith⟩
      exact lt_of_le_of_lt (hmono2 hxi hzi hzx) hfx
  · -- membership in the ball of radius `2 r`
    have hb : ‖(z, y)‖ < 2 * r := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_lt hz_abs hy_abs
    simpa [Metric.mem_ball, dist_eq_norm] using hb

end Work.RPB.B1a
