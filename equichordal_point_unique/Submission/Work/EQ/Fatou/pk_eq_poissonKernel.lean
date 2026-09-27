import Mathlib
import Submission.Work.EQ.FatouDefs

namespace Work.EQ.Fatou

open Complex

theorem pk_eq_poissonKernel (r θ ψ : ℝ) (hr1 : r < 1) :
    Work.EQ.pk r (θ - ψ) = poissonKernel 0 (r * Complex.exp ((θ : ℂ) * Complex.I))
      (Complex.exp ((ψ : ℂ) * Complex.I)) := by
  rw [Work.EQ.pk, poissonKernel]
  have hz : ‖Complex.exp ((ψ:ℂ)*Complex.I) - 0‖ ^ 2 = 1 := by
    rw [sub_zero, Complex.sq_norm, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hw : ‖(r:ℂ) * Complex.exp ((θ:ℂ)*Complex.I) - 0‖ ^ 2 = r^2 := by
    rw [sub_zero, Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    ring
  have hzw :
      ‖(Complex.exp ((ψ:ℂ)*Complex.I) - 0) - ((r:ℂ) * Complex.exp ((θ:ℂ)*Complex.I) - 0)‖ ^ 2
      = 1 - 2*r*Real.cos (θ - ψ) + r^2 := by
    rw [sub_zero, sub_zero, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_mul,
        Complex.normSq_ofReal]
    simp [Complex.normSq_eq_norm_sq, Complex.exp_ofReal_mul_I, Real.cos_sub,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    ring
  rw [hz, hw, hzw]

end Work.EQ.Fatou
