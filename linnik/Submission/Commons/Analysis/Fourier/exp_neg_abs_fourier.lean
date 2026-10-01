import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Fourier transform of the two-sided exponential

We compute, for `ε > 0` and `ω : ℝ`,
`∫ τ : ℝ, exp (-(ε * |τ|)) * exp (-(τ * ω * I)) = 2 * ε / (ε ^ 2 + ω ^ 2)`.

This is the classical Fourier transform of `τ ↦ exp (-ε * |τ|)`.  Splitting the integral
at `0` and using the elementary halves `∫_{Ioi 0} exp (a * x) = -1 / a` (for `a.re < 0`) and
`∫_{Iic 0} exp (a * x) = 1 / a` (for `0 < a.re`) with `a = -ε - I * ω` and `a = ε - I * ω`
respectively, the result follows by a routine algebraic simplification.
-/

open MeasureTheory Set Complex

namespace Commons.Analysis.Fourier

theorem exp_neg_abs_fourier {ε ω : ℝ} (hε : 0 < ε) :
    ∫ τ : ℝ, Complex.exp (-(ε * |τ|)) * Complex.exp (-((((τ * ω : ℝ) : ℂ)) * Complex.I))
      = ((2 * ε / (ε ^ 2 + ω ^ 2) : ℝ) : ℂ) := by
  have hIoi : Set.EqOn (fun τ : ℝ => Complex.exp (-(ε * |τ|)) *
        Complex.exp (-((((τ * ω : ℝ) : ℂ)) * Complex.I)))
      (fun τ : ℝ => Complex.exp ((-(ε:ℂ) - (ω:ℂ) * Complex.I) * (τ:ℂ))) (Set.Ioi 0) := by
    intro τ hτ
    simp only [Set.mem_Ioi] at hτ
    simp only []
    rw [abs_of_pos hτ, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hIic : Set.EqOn (fun τ : ℝ => Complex.exp (-(ε * |τ|)) *
        Complex.exp (-((((τ * ω : ℝ) : ℂ)) * Complex.I)))
      (fun τ : ℝ => Complex.exp (((ε:ℂ) - (ω:ℂ) * Complex.I) * (τ:ℂ))) (Set.Iic 0) := by
    intro τ hτ
    simp only [Set.mem_Iic] at hτ
    simp only []
    rw [abs_of_nonpos hτ, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have ha : (-(ε:ℂ) - (ω:ℂ) * Complex.I).re < 0 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, sub_zero]
    linarith
  have hb : 0 < ((ε:ℂ) - (ω:ℂ) * Complex.I).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, sub_zero]
    exact hε
  have hIntIoi : IntegrableOn (fun τ : ℝ => Complex.exp (-(ε * |τ|)) *
      Complex.exp (-((((τ * ω : ℝ) : ℂ)) * Complex.I))) (Set.Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (a := -(ε:ℂ) - (ω:ℂ) * Complex.I) ha 0).congr_fun
      hIoi.symm measurableSet_Ioi
  have hIntIic : IntegrableOn (fun τ : ℝ => Complex.exp (-(ε * |τ|)) *
      Complex.exp (-((((τ * ω : ℝ) : ℂ)) * Complex.I))) (Set.Iic 0) :=
    (integrableOn_exp_mul_complex_Iic (a := (ε:ℂ) - (ω:ℂ) * Complex.I) hb 0).congr_fun
      hIic.symm measurableSet_Iic
  have hInt : Integrable (fun τ : ℝ => Complex.exp (-(ε * |τ|)) *
      Complex.exp (-((((τ * ω : ℝ) : ℂ)) * Complex.I))) := by
    have h := hIntIoi.union hIntIic
    rw [Set.Ioi_union_Iic] at h
    simpa only [IntegrableOn, Measure.restrict_univ] using h
  rw [← integral_add_compl (s := Set.Ioi 0) measurableSet_Ioi hInt, Set.compl_Ioi]
  rw [setIntegral_congr_fun measurableSet_Ioi hIoi,
    setIntegral_congr_fun measurableSet_Iic hIic]
  rw [integral_exp_mul_complex_Ioi (a := -(ε:ℂ) - (ω:ℂ) * Complex.I) ha 0,
    integral_exp_mul_complex_Iic (a := (ε:ℂ) - (ω:ℂ) * Complex.I) hb 0]
  have hA : ((ε:ℂ) - (ω:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im] at this
    linarith
  have hB : (-(ε:ℂ) - (ω:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at this
    linarith
  have hD : (ε:ℂ)^2 + (ω:ℂ)^2 ≠ 0 := by
    have h : (0:ℝ) < ε^2 + ω^2 := by positivity
    have : ((ε^2 + ω^2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h
    simpa using this
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [Complex.ofReal_div]
  push_cast
  field_simp
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [sq, Complex.I_mul_I]]
  ring

end Commons.Analysis.Fourier