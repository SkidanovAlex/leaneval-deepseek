import Mathlib
import Submission.Work.Cert.Spec

namespace Work.Cert.ACTrig

/-- The chord subtended by two points `e^{2πiu}`, `e^{2πiv}` of the unit circle has length
`2|sin (π(u-v))|`.  (Standard `exp`-difference computation: factor out the midpoint phase
`e^{πi(u+v)}` and use `exp (iθ) - exp (-iθ) = 2i sin θ`.) -/
theorem rot_chord (u v : ℝ) : ‖Submission.CDTPlan.rot u - Submission.CDTPlan.rot v‖ = 2 * |Real.sin (Real.pi * (u - v))| := by
  -- rewrite `rot t = exp (I * ↑(2πt))`
  have hrot : ∀ t : ℝ,
      Submission.CDTPlan.rot t = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    intro t
    rw [Submission.CDTPlan.rot]
    congr 1
    push_cast
    ring
  rw [hrot u, hrot v]
  -- factor out the midpoint phase `exp (I * ↑(2πv))`
  have key :
      Complex.exp (Complex.I * ((2 * Real.pi * u : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((2 * Real.pi * v : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * v : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * ((2 * Real.pi * u - 2 * Real.pi * v : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [key, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  -- `(2πu - 2πv)/2 = π(u-v)`
  rw [show (2 * Real.pi * u - 2 * Real.pi * v) / 2 = Real.pi * (u - v) by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

end Work.Cert.ACTrig
