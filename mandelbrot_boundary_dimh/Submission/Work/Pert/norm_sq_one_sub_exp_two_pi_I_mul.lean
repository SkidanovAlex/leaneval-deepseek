import Mathlib

namespace Work.Pert

theorem norm_sq_one_sub_exp_two_pi_I_mul (z : ℂ) :
    ‖1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)‖ ^ 2
      = (1 - Real.exp (-2 * Real.pi * z.im)) ^ 2
        + 4 * Real.exp (-2 * Real.pi * z.im) * Real.sin (Real.pi * z.re) ^ 2 := by
  -- Half-angle identity: 4 sin(π x)² = 2 - 2 cos(2π x).
  have htrig : Real.sin (Real.pi * z.re) ^ 2
      = 1 / 2 - Real.cos (Real.pi * z.re * 2) / 2 := by
    have h1 := Real.sin_sq (Real.pi * z.re)
    have h2 := Real.cos_sq (Real.pi * z.re)
    have h3 : (2 : ℝ) * (Real.pi * z.re) = Real.pi * z.re * 2 := by ring
    rw [h3] at h2
    linarith
  -- Real and imaginary parts of exp(2πi z).
  have hre : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)).re
      = Real.exp (-2 * Real.pi * z.im) * Real.cos (2 * Real.pi * z.re) := by
    rw [Complex.exp_re]; norm_num
  have him : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)).im
      = Real.exp (-2 * Real.pi * z.im) * Real.sin (2 * Real.pi * z.re) := by
    rw [Complex.exp_im]; norm_num
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, hre, him]
  ring_nf
  rw [show Real.sin (Real.pi * z.re * 2) ^ 2
        = 1 - Real.cos (Real.pi * z.re * 2) ^ 2 by
      linarith [Real.sin_sq_add_cos_sq (Real.pi * z.re * 2)], htrig]
  ring

end Work.Pert
