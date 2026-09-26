import Mathlib

namespace Work.CKFinal.Socket

/-- Key geometric estimate: for `Re w ≥ 1`, the point `1 + w` is at least as far from `4`
as `w` is from `3`, i.e. `‖w - 3‖ ≤ ‖1 + w‖`. -/
private lemma norm_sub_le (w : ℂ) (h : 1 ≤ w.re) : ‖w - 3‖ ≤ ‖1 + w‖ := by
  have hsq : ‖w - 3‖ ^ 2 ≤ ‖1 + w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im]
    norm_num
    nlinarith [h]
  have h2 := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h2

theorem disc_B_ge (w : ℂ) (h : 1 ≤ w.re) : ‖w / (1 + w) - 3 / 4‖ ≤ 1 / 4 := by
  have hz : (1 + w) ≠ 0 := by
    intro hh
    have h1 : (1 + w).re = 0 := by rw [hh]; simp
    simp only [Complex.add_re, Complex.one_re] at h1
    linarith
  have hpos : (0 : ℝ) < ‖1 + w‖ := norm_pos_iff.mpr hz
  have hkey : ‖w - 3‖ ≤ ‖1 + w‖ := norm_sub_le w h
  have hmain : w / (1 + w) - 3 / 4 = (w - 3) / (4 * (1 + w)) := by
    field_simp
    ring
  rw [hmain, norm_div, norm_mul, Complex.norm_ofNat]
  rw [div_le_iff₀ (mul_pos (by norm_num) hpos)]
  nlinarith [hkey]

end Work.CKFinal.Socket
