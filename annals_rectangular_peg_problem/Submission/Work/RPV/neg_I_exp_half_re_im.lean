import Mathlib

namespace Work.RPV

theorem neg_I_exp_half_re_im (φ r : ℝ) :
    (-(Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I)) * (r : ℂ)).re
        = -r * Real.sin (φ / 2) ∧
    (-(Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I)) * (r : ℂ)).im
        = -r * Real.cos (φ / 2) := by
  constructor <;>
  simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Real.cos_neg, Real.sin_neg] <;> ring

end Work.RPV
