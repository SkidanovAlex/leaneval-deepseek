import Mathlib

/-!
# The disc `B2` inequality

For `w : ℂ` with `1 ≤ w.re`, the point `w / (1 + 2 * w)` lies in the closed disc of
radius `1/4` centred at `1/4`.

Writing `w = x + i y` with `x ≥ 1`,

* `w / (1 + 2 * w) - 1 / 4 = (2 w - 1) / (4 (1 + 2 w))`;
* `normSq (2 w - 1) = (2x - 1)^2 + (2y)^2` and `normSq (1 + 2 w) = (2x + 1)^2 + (2y)^2`,
  so `normSq (2 w - 1) ≤ normSq (1 + 2 w)` because `|2x - 1| ≤ 2x + 1` for `x ≥ 0`.

Hence `‖(2 w - 1) / (4 (1 + 2 w))‖ ≤ 1/4`.
-/

namespace Work.CKFinal.Socket

theorem disc_B2_ge (w : ℂ) (h : 1 ≤ w.re) : ‖w / (1 + 2 * w) - 1 / 4‖ ≤ 1 / 4 := by
  have hre : (1 + 2 * w).re = 1 + 2 * w.re := by
    simp [Complex.add_re, Complex.mul_re]
  have hden : (1 : ℂ) + 2 * w ≠ 0 := by
    intro hz
    have h0 := congrArg Complex.re hz
    rw [hre, Complex.zero_re] at h0
    linarith
  have hden2 : (1 : ℂ) + w * 2 ≠ 0 := by
    rw [mul_comm w 2]; exact hden
  -- Clear denominators.
  have hid : w / (1 + 2 * w) - 1 / 4 = (2 * w - 1) / (4 * (1 + 2 * w)) := by
    field_simp [hden2]
    ring
  rw [hid]
  -- The two squared norms, in terms of the real and imaginary parts.
  have e1 : Complex.normSq (2 * w - 1) = (2 * w.re - 1) ^ 2 + (2 * w.im) ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    ring
  have e2 : Complex.normSq (1 + 2 * w) = (1 + 2 * w.re) ^ 2 + (2 * w.im) ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  have hkey : Complex.normSq (2 * w - 1) ≤ Complex.normSq (1 + 2 * w) := by
    rw [e1, e2]
    nlinarith [h]
  have hpos : 0 < Complex.normSq (1 + 2 * w) := Complex.normSq_pos.mpr hden
  -- Reduce to a `normSq` estimate.
  have hq : Complex.normSq ((2 * w - 1) / (4 * (1 + 2 * w))) =
      Complex.normSq (2 * w - 1) / (16 * Complex.normSq (1 + 2 * w)) := by
    rw [Complex.normSq_div, Complex.normSq_mul]
    norm_num [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
  have h4 : Complex.normSq ((2 * w - 1) / (4 * (1 + 2 * w))) ≤ 1 / 16 := by
    rw [hq, div_le_iff₀ (by linarith)]
    nlinarith [hkey, Complex.normSq_nonneg (2 * w - 1)]
  -- Convert to the norm bound.
  have hz2 : ‖(2 * w - 1) / (4 * (1 + 2 * w))‖ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, show (1 / 4 : ℝ) ^ 2 = 1 / 16 by norm_num]
    exact h4
  have hfin : |‖(2 * w - 1) / (4 * (1 + 2 * w))‖| ≤ |(1 / 4 : ℝ)| := sq_le_sq.mp hz2
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hfin

end Work.CKFinal.Socket
