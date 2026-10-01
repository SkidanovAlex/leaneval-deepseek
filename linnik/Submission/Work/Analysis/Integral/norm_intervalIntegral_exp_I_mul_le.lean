import Mathlib

namespace Work.Analysis.Integral

/-- The integral of `exp (I * θ * t)` over `[0, T]` has modulus at most `2 / |θ|`:
the primitive is `exp (I * θ * t) / (I * θ)`, and `‖exp (I * x)‖ = 1`. -/
lemma norm_intervalIntegral_exp_I_mul_le (T θ : ℝ) (hθ : θ ≠ 0) :
    ‖∫ t in (0 : ℝ)..T, Complex.exp (Complex.I * ((θ * t : ℝ) : ℂ))‖ ≤ 2 / |θ| := by
  have hc : Complex.I * (θ : ℂ) ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact Complex.I_ne_zero h1
    · exact hθ (Complex.ofReal_eq_zero.mp h2)
  have hfun : (fun t : ℝ => Complex.exp (Complex.I * ((θ * t : ℝ) : ℂ)))
      = fun t : ℝ => Complex.exp ((Complex.I * (θ : ℂ)) * (t : ℂ)) := by
    funext t
    congr 1
    rw [Complex.ofReal_mul]
    ring
  rw [hfun, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hcnorm : ‖Complex.I * (θ : ℂ)‖ = |θ| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hz : ‖Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ))‖ = 1 := by
    have : Complex.I * (θ : ℂ) * (T : ℂ) = Complex.I * ((θ * T : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul]; ring
    rw [this, Complex.norm_exp_I_mul_ofReal]
  have hb : ‖Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ)) - 1‖ ≤ 2 := by
    calc ‖Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ)) - 1‖
        ≤ ‖Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hz, norm_one]; norm_num
  calc ‖(Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ)) - 1) / (Complex.I * (θ : ℂ))‖
      = ‖Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ)) - 1‖ / ‖Complex.I * (θ : ℂ)‖ := norm_div _ _
    _ = ‖Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ)) - 1‖ / |θ| := by rw [hcnorm]
    _ ≤ 2 / |θ| := div_le_div_of_nonneg_right hb (abs_nonneg θ)

end Work.Analysis.Integral
