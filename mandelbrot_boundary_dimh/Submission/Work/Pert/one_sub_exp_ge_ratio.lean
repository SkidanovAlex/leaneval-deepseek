import Mathlib
import Submission.Work.Pert.norm_ratio_exp_sub_one_le

namespace Work.Pert

/-- **Lower bound for `1 - exp z` on the disc of radius `1/2`.**

For `‖z‖ ≤ 1/2` we have `(25/36) ‖z‖ ≤ ‖1 - exp z‖`. Since `(exp z - 1)/z = 1 + O(‖z‖)`
with `‖(exp z - 1)/z - 1‖ ≤ 11/36` on that disc (`norm_ratio_exp_sub_one_le`), the reverse
triangle inequality gives `‖(exp z - 1)/z‖ ≥ 1 - 11/36 = 25/36`, and multiplying by `‖z‖`
yields the claim. -/
theorem one_sub_exp_ge_ratio {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    (25 / 36 : ℝ) * ‖z‖ ≤ ‖1 - Complex.exp z‖ := by
  rcases eq_or_ne z 0 with h | hz0
  · subst h; simp
  have hr : 0 < ‖z‖ := by rw [norm_pos_iff]; exact hz0
  have hw : ‖(Complex.exp z - 1) / z - 1‖ ≤ 11 / 36 :=
    norm_ratio_exp_sub_one_le hz0 hz
  have h1 : (25 / 36 : ℝ) ≤ ‖(Complex.exp z - 1) / z‖ := by
    have hsplit : (Complex.exp z - 1) / z = 1 + ((Complex.exp z - 1) / z - 1) := by ring
    rw [hsplit]
    have htri := norm_sub_norm_le (1 : ℂ) (-((Complex.exp z - 1) / z - 1))
    simp only [norm_one, norm_neg] at htri
    rw [sub_neg_eq_add] at htri
    linarith
  have hmul : (25 / 36 : ℝ) * ‖z‖ ≤ ‖(Complex.exp z - 1) / z‖ * ‖z‖ :=
    mul_le_mul_of_nonneg_right h1 hr.le
  have heq : ‖(Complex.exp z - 1) / z‖ * ‖z‖ = ‖1 - Complex.exp z‖ := by
    rw [← norm_mul]
    have hcancel : (Complex.exp z - 1) / z * z = Complex.exp z - 1 := by
      field_simp
    rw [hcancel, show (1 : ℂ) - Complex.exp z = -(Complex.exp z - 1) by ring, norm_neg]
  linarith [hmul, heq.le, heq.ge]

end Work.Pert
