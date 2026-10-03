import Mathlib

namespace Work.Repel

/-- If `u` is within `η/40` of `w`, and `‖w‖ ≥ η - 1/8` with `η ≥ 100`, then the
reciprocal shift `-1/u + 1/w` is bounded by `1/(38η)`. -/
theorem inv_shift_close {η : ℝ} (hη : 100 ≤ η) {u w : ℂ}
    (huw : ‖u - w‖ ≤ η / 40) (hw : η - 1 / 8 ≤ ‖w‖) :
    ‖-1 / u + 1 / w‖ ≤ 1 / (38 * η) := by
  have h38pos : (0 : ℝ) < 38 * η := by linarith
  have hC : (0 : ℝ) < η - 1 / 8 := by linarith
  have hB : (0 : ℝ) < 39 * η / 40 - 1 / 8 := by linarith
  have hu_low : 39 * η / 40 - 1 / 8 ≤ ‖u‖ := by
    have h2 := norm_sub_norm_le w u
    rw [norm_sub_rev w u] at h2
    linarith
  have hu_pos : (0 : ℝ) < ‖u‖ := lt_of_lt_of_le hB hu_low
  have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
  have hunz : u ≠ 0 := norm_pos_iff.mp hu_pos
  have hwnz : w ≠ 0 := norm_pos_iff.mp hw_pos
  have hkey : -1 / u + 1 / w = (u - w) / (u * w) := by
    rw [div_add_div _ _ hunz hwnz]
    congr 1
    ring
  rw [hkey, norm_div, norm_mul, div_le_div_iff₀ (mul_pos hu_pos hw_pos) h38pos]
  have h1 : ‖u - w‖ * (38 * η) ≤ (η / 40) * (38 * η) :=
    mul_le_mul_of_nonneg_right huw (by linarith)
  have h2 : (η / 40) * (38 * η) ≤ (39 * η / 40 - 1 / 8) * (η - 1 / 8) := by
    nlinarith [hη]
  have h3 : (39 * η / 40 - 1 / 8) * (η - 1 / 8) ≤ ‖u‖ * ‖w‖ :=
    mul_le_mul hu_low hw (le_of_lt hC) (norm_nonneg u)
  linarith

end Work.Repel
