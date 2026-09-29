import Mathlib

namespace Work.OdeCont

set_option linter.unusedVariables false in
theorem circle_midpoint {r0 ρ δ : ℝ} {z w : ℂ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hδ' : δ < ρ - r0) (hz : ‖z‖ = ρ) (hw : ‖w‖ = ρ) (hne : z ≠ w) (hclose : ‖z - w‖ < 2 * δ) :
    ‖(z + w) / 2 - z‖ < δ ∧ ‖(z + w) / 2 - w‖ < δ ∧
      r0 < ‖(z + w) / 2‖ ∧ ‖(z + w) / 2‖ < ρ := by
  have hpos : 0 < ‖z - w‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hne
  have hhalf : ‖z - w‖ / 2 < δ := by linarith
  have hnorm_z : ‖(z + w) / 2 - z‖ = ‖z - w‖ / 2 := by
    rw [show (z + w) / 2 - z = (w - z) / 2 by ring, norm_div]
    rw [show w - z = -(z - w) by ring, norm_neg]
    norm_num
  have hnorm_w : ‖(z + w) / 2 - w‖ = ‖z - w‖ / 2 := by
    rw [show (z + w) / 2 - w = (z - w) / 2 by ring, norm_div]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hnorm_z]; exact hhalf
  · rw [hnorm_w]; exact hhalf
  · have h1 : ‖z‖ ≤ ‖(z + w) / 2‖ + ‖(z + w) / 2 - z‖ := by
      have hz' : z = (z + w) / 2 - ((z + w) / 2 - z) := by ring
      calc ‖z‖ = ‖(z + w) / 2 - ((z + w) / 2 - z)‖ := by rw [← hz']
        _ ≤ ‖(z + w) / 2‖ + ‖(z + w) / 2 - z‖ := norm_sub_le _ _
    rw [hz, hnorm_z] at h1
    linarith
  · have hp := parallelogram_law_with_norm ℂ z w
    rw [hz, hw] at hp
    have hlt : ‖z + w‖ < 2 * ρ := by
      nlinarith [norm_nonneg (z + w), hρ.le, hp, pow_pos hpos 2]
    rw [show ‖(z + w) / 2‖ = ‖z + w‖ / 2 by rw [norm_div]; norm_num]
    linarith

end Work.OdeCont
