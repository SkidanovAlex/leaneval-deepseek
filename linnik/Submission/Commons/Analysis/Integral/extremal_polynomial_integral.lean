import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory intervalIntegral Set

namespace Commons.Analysis.Integral

/-- The (unweighted) integral of the basic extremal polynomial on `[0,2]`. -/
private lemma integral_poly_const :
    (∫ u in (0:ℝ)..2, (2-u)^3 * (4 + 6*u + u^2)) = 80/3 := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 2,
      HasDerivAt (fun u : ℝ => 32*u - (40/3)*u^3 + 5*u^4 - u^6/6)
        ((2-x)^3 * (4 + 6*x + x^2)) x := by
    intro x hx
    have h1 : HasDerivAt (fun u : ℝ => 32*u) 32 x := by
      simpa using (hasDerivAt_id x).const_mul (32:ℝ)
    have h2 : HasDerivAt (fun u : ℝ => (40/3)*u^3) ((40/3)*((3:ℝ)*x^(3-1))) x :=
      (hasDerivAt_pow 3 x).const_mul (40/3)
    have h3 : HasDerivAt (fun u : ℝ => 5*u^4) (5*((4:ℝ)*x^(4-1))) x :=
      (hasDerivAt_pow 4 x).const_mul (5:ℝ)
    have h4 : HasDerivAt (fun u : ℝ => u^6/6) (((6:ℝ)*x^(6-1))/6) x :=
      (hasDerivAt_pow 6 x).div_const 6
    have h := ((h1.sub h2).add h3).sub h4
    exact h.congr_deriv (by norm_num; ring)
  have hint : IntervalIntegrable (fun x : ℝ => (2-x)^3 * (4 + 6*x + x^2)) volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

/-- The exponential-weighted integral of the basic extremal polynomial on `[0,2]`. -/
private lemma integral_exp_poly_const :
    (∫ u in (0:ℝ)..2, Real.exp u * ((2-u)^3 * (4 + 6*u + u^2))) = 48 := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 2,
      HasDerivAt (fun u : ℝ => Real.exp u * (-48 + 80*u - 40*u^2 + 5*u^4 - u^5))
        (Real.exp x * ((2-x)^3 * (4 + 6*x + x^2))) x := by
    intro x hx
    have hR : HasDerivAt (fun u : ℝ => -48 + 80*u - 40*u^2 + 5*u^4 - u^5)
        (80 - 80*x + 20*x^3 - 5*x^4) x := by
      have h0 : HasDerivAt (fun _ : ℝ => (-48:ℝ)) 0 x := hasDerivAt_const x (-48)
      have h1 : HasDerivAt (fun u : ℝ => 80*u) 80 x := by
        simpa using (hasDerivAt_id x).const_mul (80:ℝ)
      have h2 : HasDerivAt (fun u : ℝ => 40*u^2) (40*((2:ℝ)*x^(2-1))) x :=
        (hasDerivAt_pow 2 x).const_mul (40:ℝ)
      have h3 : HasDerivAt (fun u : ℝ => 5*u^4) (5*((4:ℝ)*x^(4-1))) x :=
        (hasDerivAt_pow 4 x).const_mul (5:ℝ)
      have h4 : HasDerivAt (fun u : ℝ => u^5) ((5:ℝ)*x^(5-1)) x :=
        hasDerivAt_pow 5 x
      have h := (((h0.add h1).sub h2).add h3).sub h4
      exact h.congr_deriv (by norm_num; ring)
    have h := (Real.hasDerivAt_exp x).mul hR
    exact h.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp x * ((2-x)^3 * (4 + 6*x + x^2))) volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

theorem extremal_polynomial_integral {lam : ℝ} (hlam : 0 < lam) :
    (∫ x in (0:ℝ)..(2/lam), (lam/30) * (2 - lam*x)^3 * (4 + 6*lam*x + (lam*x)^2)) = 8/9 ∧
    (∫ x in (0:ℝ)..(2/lam), Real.exp (lam*x) * ((lam/30) * (2 - lam*x)^3 * (4 + 6*lam*x + (lam*x)^2))) = 8/5 := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  constructor
  · rw [show (∫ x in (0:ℝ)..(2/lam), (lam/30) * (2 - lam*x)^3 * (4 + 6*lam*x + (lam*x)^2))
         = ∫ x in (0:ℝ)..(2/lam), (lam/30) * ((2 - lam*x)^3 * (4 + 6*(lam*x) + (lam*x)^2)) by
          apply intervalIntegral.integral_congr; intro x hx; ring]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_mul_left (fun u : ℝ => (2-u)^3 * (4 + 6*u + u^2)) hne]
    simp only [mul_zero, smul_eq_mul]
    have hb : lam * (2/lam) = 2 := by field_simp
    rw [hb, integral_poly_const]
    field_simp
    ring
  · rw [show (∫ x in (0:ℝ)..(2/lam), Real.exp (lam*x) * ((lam/30) * (2 - lam*x)^3 * (4 + 6*lam*x + (lam*x)^2)))
         = ∫ x in (0:ℝ)..(2/lam), (fun u : ℝ => Real.exp u * ((lam/30) * ((2-u)^3 * (4 + 6*u + u^2)))) (lam*x) by
          apply intervalIntegral.integral_congr; intro x hx; ring]
    rw [intervalIntegral.integral_comp_mul_left (fun u : ℝ => Real.exp u * ((lam/30) * ((2-u)^3 * (4 + 6*u + u^2)))) hne]
    simp only [mul_zero, smul_eq_mul]
    have hb : lam * (2/lam) = 2 := by field_simp
    rw [hb]
    rw [show (∫ u in (0:ℝ)..2, Real.exp u * ((lam/30) * ((2-u)^3 * (4 + 6*u + u^2))))
         = (lam/30) * (∫ u in (0:ℝ)..2, Real.exp u * ((2-u)^3 * (4 + 6*u + u^2))) by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr; intro x hx; ring]
    rw [integral_exp_poly_const]
    field_simp
    ring

end Commons.Analysis.Integral