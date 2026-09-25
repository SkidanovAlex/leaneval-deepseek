import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Submission.Commons.Analysis.Integral.riemann_sum_sub_integral_le

namespace Commons.Analysis.ExponentialSums

open MeasureTheory Finset
open scoped BigOperators

/-- The function `t ↦ exp(2πi a t²)` is differentiable with derivative
`exp(2πi a t²) · 2πi · (2 a t)`. -/
private lemma hasDerivAt_exp_quad (a t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((a * t^2 : ℝ) : ℂ)))
      (Complex.exp (2 * Real.pi * Complex.I * ((a * t^2 : ℝ) : ℂ)) *
        (2 * Real.pi * Complex.I * ((a * (2*t) : ℝ) : ℂ))) t := by
  have hu : HasDerivAt (fun t : ℝ => a * t^2) (a * (2*t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul a
  have hu2 := hu.ofReal_comp
  have hv : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * ((a * t^2 : ℝ) : ℂ))
      (2 * Real.pi * Complex.I * ((a * (2*t) : ℝ) : ℂ)) t := by
    simpa using hu2.const_mul (2 * Real.pi * Complex.I)
  exact hv.cexp

/-- Norm bound for the derivative of `t ↦ exp(2πi a t²)` on `[0,1]`. -/
private lemma norm_deriv_exp_quad_le (a t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((a * t^2 : ℝ) : ℂ)) *
        (2 * Real.pi * Complex.I * ((a * (2*t) : ℝ) : ℂ))‖ ≤ 4 * Real.pi * |a| := by
  have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * ((a * t^2 : ℝ) : ℂ))‖ = 1 := by
    rw [show 2 * Real.pi * Complex.I * ((a * t^2 : ℝ) : ℂ)
        = ((2 * Real.pi * (a * t^2) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.norm_exp_ofReal_mul_I]
  have h2 : ‖2 * Real.pi * Complex.I * ((a * (2*t) : ℝ) : ℂ)‖ = 2 * Real.pi * |a * (2*t)| := by
    rw [show 2 * Real.pi * Complex.I * ((a * (2*t) : ℝ) : ℂ)
        = ((2 * Real.pi * (a * (2*t)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.norm_mul, Complex.norm_I, mul_one,
        show ‖(((2 * Real.pi * (a * (2*t)) : ℝ)) : ℂ)‖ = |2 * Real.pi * (a * (2*t))| from
          RCLike.norm_ofReal _]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  rw [Complex.norm_mul, hexp, one_mul, h2]
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hat : |a * (2*t)| = |a| * (2*t) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2*t)]
  rw [hat]
  have hkey : 2 * Real.pi * |a| * (2*t) ≤ 2 * Real.pi * |a| * 2 :=
    mul_le_mul_of_nonneg_left (by linarith : 2*t ≤ 2) (by positivity)
  nlinarith [hkey, abs_nonneg a, Real.pi_pos]

/-- Comparison of the `β`-oscillating quadratic sum with its continuous analogue:
`|(1/P) ∑_{p<P} e(c p²) − ∫_0^1 e(c P² s²) ds| ≤ 4π|c|P`.  This is the step that
replaces the `β`-sum on the major arcs by the oscillatory integral `v_t(β)`. -/
theorem sum_exp_quadratic_vs_integral (P : ℕ) (hP : 0 < P) (c : ℝ) :
    ‖(P : ℂ)⁻¹ * ∑ p ∈ Finset.range P,
        Complex.exp (2 * Real.pi * Complex.I * ((c * (p : ℝ) ^ 2 : ℝ) : ℂ))
      - ∫ s in (0 : ℝ)..1,
          Complex.exp (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * s ^ 2 : ℝ) : ℂ))‖
    ≤ 4 * Real.pi * |c| * (P : ℝ) := by
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hPne : (P : ℝ) ≠ 0 := ne_of_gt hPpos
  have hsum : ∀ p : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * ((p : ℝ) / (P : ℝ)) ^ 2 : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * ((c * (p : ℝ) ^ 2 : ℝ) : ℂ)) := by
    intro p
    congr 2
    field_simp
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * t^2 : ℝ) : ℂ)))
        (Complex.exp (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * t^2 : ℝ) : ℂ)) *
          (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * (2*t) : ℝ) : ℂ))) t :=
    fun t _ => hasDerivAt_exp_quad (c * (P : ℝ) ^ 2) t
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Complex.exp (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * t^2 : ℝ) : ℂ)) *
          (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * (2*t) : ℝ) : ℂ))‖
        ≤ 4 * Real.pi * |c * (P : ℝ) ^ 2| :=
    fun t ht => norm_deriv_exp_quad_le (c * (P : ℝ) ^ 2) t ht
  have hM : (0 : ℝ) ≤ 4 * Real.pi * |c * (P : ℝ) ^ 2| := by positivity
  have hcom := Commons.Analysis.Integral.riemann_sum_sub_integral_le
    (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * t^2 : ℝ) : ℂ)))
    (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * t^2 : ℝ) : ℂ)) *
          (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * (2*t) : ℝ) : ℂ)))
    hM hderiv hbound P hP
  rw [show (∑ p ∈ Finset.range P,
        Complex.exp (2 * Real.pi * Complex.I * ((c * (P : ℝ) ^ 2 * ((p : ℝ) / (P : ℝ)) ^ 2 : ℝ) : ℂ)))
      = ∑ p ∈ Finset.range P,
        Complex.exp (2 * Real.pi * Complex.I * ((c * (p : ℝ) ^ 2 : ℝ) : ℂ)) from
      Finset.sum_congr rfl (fun p _ => hsum p)] at hcom
  have hR : (4 * Real.pi * |c * (P : ℝ) ^ 2|) / (P : ℝ) = 4 * Real.pi * |c| * (P : ℝ) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (P : ℝ))]
    field_simp
  exact le_trans hcom (le_of_eq hR)

end Commons.Analysis.ExponentialSums