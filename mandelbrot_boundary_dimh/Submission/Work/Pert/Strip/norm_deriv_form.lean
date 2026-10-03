import Mathlib
import Submission.Work.Pert.Strip.Defs

namespace Work.Pert.Strip

noncomputable section

/-- The norm of a real number seen as a complex number. -/
lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h1 : ‖(r : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, sq_abs]
    ring
  have h2 : 0 ≤ ‖(r : ℂ)‖ := norm_nonneg _
  have h3 : 0 ≤ |r| := abs_nonneg _
  nlinarith

/-- The norm of the chart coefficient is the real coefficient. -/
lemma norm_chartC {h : ℝ} (hh : 0 < h) : ‖chartC h‖ = chartK h := by
  rw [chartC_eq_ofReal, norm_mul, Complex.norm_I, one_mul, norm_ofReal_eq_abs,
    abs_of_pos (chartK_pos hh)]

/-- The modulus of the exponential factor is `chartR`. -/
lemma norm_chartExp (h : ℝ) (ζ : ℂ) : ‖chartExp h ζ‖ = chartR h ζ := by
  rw [chartExp, chartR, Complex.norm_exp]
  congr 1
  rw [chartC_eq_ofReal, mul_assoc, Complex.I_mul_re]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

theorem norm_deriv_form {h : ℝ} (hh : 0 < h) (ζ : ℂ) :
    ‖2 * chartC h * chartExp h ζ / (chartExp h ζ + 1) ^ 2‖
      = 2 * chartK h * chartR h ζ / ‖chartExp h ζ + 1‖ ^ 2 := by
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_chartC hh, norm_chartExp]
  norm_num

end

end Work.Pert.Strip
