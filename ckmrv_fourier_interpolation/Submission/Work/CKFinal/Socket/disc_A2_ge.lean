import Mathlib

namespace Work.CKFinal.Socket

/-- Auxiliary: the key geometric inequality. For `z : ℂ` with `1 ≤ z.re`, the
point `z` is at least as far from the origin as from `z - 2`. Phrased here for
`w` with `1 ≤ w.re`, i.e. `‖2w - 3‖ ≤ ‖1 - 2w‖`. -/
private theorem norm_two_mul_sub_three_le (w : ℂ) (h : 1 ≤ w.re) :
    ‖(2 : ℂ) * w - 3‖ ≤ ‖1 - 2 * w‖ := by
  have hsq : Complex.normSq ((2 : ℂ) * w - 3) ≤ Complex.normSq (1 - 2 * w) := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    norm_num
    nlinarith [h]
  have h2 : ‖(2 : ℂ) * w - 3‖ ^ 2 ≤ ‖1 - 2 * w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact hsq
  have := sq_le_sq.mp h2
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at this

theorem disc_A2_ge (w : ℂ) (h : 1 ≤ w.re) : ‖w / (1 - 2 * w) + 3 / 4‖ ≤ 1 / 4 := by
  have key : ‖(2 : ℂ) * w - 3‖ ≤ ‖1 - 2 * w‖ := norm_two_mul_sub_three_le w h
  have hne : (1 : ℂ) - 2 * w ≠ 0 := by
    intro hc
    have : ((1 : ℂ) - 2 * w).re = 0 := by rw [hc]; simp
    rw [Complex.sub_re, Complex.mul_re] at this
    simp at this
    linarith
  have hmain : w / (1 - 2 * w) + 3 / 4 = (3 - 2 * w) / (4 * (1 - 2 * w)) := by
    rw [div_add_div (w : ℂ) (3 : ℂ) hne (by norm_num),
      show w * 4 + (1 - 2 * w) * 3 = 3 - 2 * w by ring,
      show (1 - 2 * w) * 4 = 4 * (1 - 2 * w) by ring]
  rw [hmain, norm_div, norm_mul]
  simp only [Complex.norm_ofNat]
  rw [show ‖3 - 2 * w‖ = ‖(2 : ℂ) * w - 3‖ by
    rw [show (3 : ℂ) - 2 * w = -((2 : ℂ) * w - 3) by ring, norm_neg]]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [key, norm_nonneg (1 - 2 * w)]

end Work.CKFinal.Socket
