import Mathlib

namespace Work.TMC14Core

theorem norm_le_of_im_zero_of_sq_re_le (z : ℂ) (c0 : ℝ) (him : z.im = 0)
    (h : (z ^ 2).re ≤ c0 ^ 2) : ‖z‖ ≤ ‖(c0 : ℂ)‖ := by
  have h2 : z.re ^ 2 ≤ c0 ^ 2 := by
    have : (z ^ 2).re = z.re ^ 2 := by
      rw [pow_two, Complex.mul_re, him]
      ring
    linarith [h]
  have hz2 : ‖z‖ ^ 2 = z.re ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, him]
    ring
  have hc2 : ‖(c0 : ℂ)‖ ^ 2 = c0 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  have hsq : ‖z‖ ^ 2 ≤ ‖(c0 : ℂ)‖ ^ 2 := by rw [hz2, hc2]; exact h2
  have h' := sq_le_sq.mp hsq
  rw [abs_of_nonneg (norm_nonneg z), abs_of_nonneg (norm_nonneg _)] at h'
  exact h'

end Work.TMC14Core
