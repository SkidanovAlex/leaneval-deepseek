import Mathlib
import Submission.Work.Cert.WLDefs

namespace Work.ANum3.Z2

/-- The scale `S` used in `Work.Cert.cx` is nonzero over the reals. -/
private lemma certS_ne_zero : (Work.Cert.S : ℝ) ≠ 0 := by norm_num [Work.Cert.S]

lemma cx_div_reim (ar ai br bi : ℤ) (hD : 0 < br * br + bi * bi) :
    (Work.Cert.cx ar ai / Work.Cert.cx br bi).re
        = ((ar * br + ai * bi : ℤ) : ℝ) / ((br * br + bi * bi : ℤ) : ℝ)
      ∧ (Work.Cert.cx ar ai / Work.Cert.cx br bi).im
        = ((ai * br - ar * bi : ℤ) : ℝ) / ((br * br + bi * bi : ℤ) : ℝ) := by
  have hS : (Work.Cert.S : ℝ) ≠ 0 := certS_ne_zero
  have hD' : ((br * br + bi * bi : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  constructor
  · rw [Complex.div_re]
    simp only [Work.Cert.cx, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.normSq_apply, mul_one,
      mul_zero, add_zero, sub_zero]
    push_cast
    field_simp
    ring
  · rw [Complex.div_im]
    simp only [Work.Cert.cx, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.normSq_apply, mul_one,
      mul_zero, add_zero, sub_zero]
    push_cast
    field_simp
    ring

end Work.ANum3.Z2
