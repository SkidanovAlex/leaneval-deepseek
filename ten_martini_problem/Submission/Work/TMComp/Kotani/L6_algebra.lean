import Mathlib
import Submission.Work.TMContract.Components

namespace Work.TMComp.Kotani

theorem L6_algebra (a c : ℂ) (ha : 0 < a.im) (hc : 0 < c.im) :
    1 / a.im + 1 / c.im - 4 * (-1 / (a - star c)).im
      = (a - star c).im * ‖a - c‖ ^ 2 / (a.im * c.im * ‖a - star c‖ ^ 2) := by
  -- Imaginary part of `a - conj c` and of `-1 / (a - conj c)`.
  have h1 : (a - star c).im = a.im + c.im := by
    simp only [Complex.star_def, Complex.sub_im, Complex.conj_im]
    ring
  have h2 : (-1 / (a - star c)).im = (a.im + c.im) / ‖a - star c‖ ^ 2 := by
    rw [Complex.div_im]
    simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.star_def,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.normSq_eq_norm_sq]
    ring
  -- The two squared norms differ by `4 * a.im * c.im`.
  have h3 : ‖a - c‖ ^ 2 = ‖a - star c‖ ^ 2 - 4 * (a.im * c.im) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.star_def, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    ring
  have hw : a - star c ≠ 0 := by
    intro h
    have hz : (a - star c).im = 0 := by rw [h]; simp
    rw [h1] at hz
    linarith
  have hN : (0 : ℝ) < ‖a - star c‖ ^ 2 := by
    rw [Complex.sq_norm]
    exact Complex.normSq_pos.mpr hw
  rw [h1, h2, h3]
  have ha' : a.im ≠ 0 := ne_of_gt ha
  have hc' : c.im ≠ 0 := ne_of_gt hc
  have hN' : ‖a - star c‖ ^ 2 ≠ 0 := ne_of_gt hN
  field_simp
  ring

end Work.TMComp.Kotani
