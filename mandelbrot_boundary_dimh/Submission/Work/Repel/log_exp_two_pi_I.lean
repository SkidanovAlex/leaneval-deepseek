import Mathlib

namespace Work.Repel

/-- `log (exp (2πi w)) = 2πi w` for `w.re ∈ (-1/2, 1/2]`, because then the imaginary part
`2π w.re` of `2πi w` lies in the principal branch interval `(-π, π]`. -/
theorem log_exp_two_pi_I (w : ℂ) (h₁ : -(1 / 2) < w.re) (h₂ : w.re ≤ 1 / 2) :
    Complex.log (Complex.exp (2 * Real.pi * Complex.I * w)) / (2 * Real.pi * Complex.I) = w := by
  have him : (2 * Real.pi * Complex.I * w).im = 2 * Real.pi * w.re := by
    simp [Complex.mul_im, Complex.mul_re]
  have hlog := Complex.log_exp (x := 2 * Real.pi * Complex.I * w)
    (by rw [him]; nlinarith [Real.pi_pos])
    (by rw [him]; nlinarith [Real.pi_pos])
  rw [hlog]
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Complex.I_ne_zero, Real.pi_ne_zero]
  exact mul_div_cancel_left₀ w hne

end Work.Repel
