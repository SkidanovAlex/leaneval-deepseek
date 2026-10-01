import Mathlib
import Submission.Work.LinnikAreas.A5.Basic

namespace Work.LinnikAreas.A5

/-- The elementary Laplace integral behind the first display: substituting
`sinh((K-t)λ) = (e^{λ(K-t)} - e^{-λ(K-t)})/2` turns the integrand into
`e^{Kλ}/2 - e^{-Kλ}e^{2λt}/2`, so only `∫₀^K e^{2λt} dt = (e^{2Kλ}-1)/(2λ)` is needed:
`∫₀^K e^{λt} sinh((K-t)λ) dt = e^{Kλ} (K/2 - (1-e^{-2Kλ})/(4λ))`. -/
lemma integral_exp_mul_sinh (K lam : ℝ) (hlam : 0 < lam) :
    (∫ t in (0:ℝ)..K, Real.exp (lam*t) * Real.sinh ((K-t)*lam))
      = Real.exp (K*lam) * (K/2 - (1 - Real.exp (-2*K*lam))/(4*lam)) := by
  have hint : (∫ t in (0:ℝ)..K, Real.exp (2*lam*t)) = (Real.exp (2*lam*K) - 1)/(2*lam) := by
    rw [intervalIntegral.integral_comp_mul_left (c := 2*lam) (f := fun t : ℝ => Real.exp t)
      (by positivity)]
    rw [integral_exp, smul_eq_mul, inv_mul_eq_div]
    simp only [mul_zero, Real.exp_zero]
  have hcongr : (∫ t in (0:ℝ)..K, Real.exp (lam*t) * Real.sinh ((K-t)*lam))
      = ∫ t in (0:ℝ)..K,
          (Real.exp (K*lam)/2 - Real.exp (-(K*lam))/2 * Real.exp (2*lam*t)) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have hAB : Real.exp (lam*t) * Real.exp ((K-t)*lam) = Real.exp (K*lam) := by
      rw [← Real.exp_add]; congr 1; ring
    have hAC : Real.exp (lam*t) * Real.exp (-((K-t)*lam)) = Real.exp (2*lam*t - K*lam) := by
      rw [← Real.exp_add]; congr 1; ring
    have hAC'' : Real.exp (-(K*lam))/2 * Real.exp (2*lam*t)
        = Real.exp (2*lam*t - K*lam)/2 := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      congr 1
      congr 1
      ring
    rw [Real.sinh_eq, mul_div_assoc', mul_sub, hAB, hAC, hAC'']
    ring
  rw [hcongr]
  have hInt1 : IntervalIntegrable (fun _ : ℝ => Real.exp (K*lam)/2)
      MeasureTheory.volume (0:ℝ) K := Continuous.intervalIntegrable continuous_const _ _
  have hInt2 : IntervalIntegrable (fun t : ℝ => Real.exp (-(K*lam))/2 * Real.exp (2*lam*t))
      MeasureTheory.volume (0:ℝ) K := Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_sub hInt1 hInt2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, hint]
  have hE : Real.exp (K*lam) ≠ 0 := (Real.exp_pos _).ne'
  have hexp2 : Real.exp (2*lam*K) = Real.exp (K*lam)^2 := by
    rw [show 2*lam*K = ((2:ℕ) : ℝ) * (K*lam) by ring, Real.exp_nat_mul]
  have hexpneg : Real.exp (-(K*lam)) = (Real.exp (K*lam))⁻¹ := Real.exp_neg _
  have hexpneg2 : Real.exp (-2*K*lam) = (Real.exp (K*lam)^2)⁻¹ := by
    rw [show -2*K*lam = -(((2:ℕ) : ℝ) * (K*lam)) by ring, Real.exp_neg, Real.exp_nat_mul]
  rw [hexp2, hexpneg, hexpneg2]
  field_simp
  ring

/-
The two explicit computations behind the numerical shape of HB 13.3.  With
`F1 K lam z = ∫₀^K e^{-zt} sinh((K-t)λ) dt` (`Work.LinnikAreas.A5.F1`) and `Bfun` the
per-character bound of HB 13.3 (`Work.LinnikContract.Bfun`, i.e.
K²B(λ) = (1-e^{-2Kλ})/(6λ) + (2Kλ-1+e^{-2Kλ})/(2λ²)):

(i) F₁(-λ) = e^{Kλ}(K/2 - (1-e^{-2Kλ})/(4λ));
(ii) (2/λ)e^{-Kλ}(sinh(Kλ)/6 + F₁(-λ)) = K² B(λ).

Both are elementary calculus; (i) is ∫₀^K e^{λt}sinh((K-t)λ)dt, (ii) is the algebra that turns
HB's error terms into his displayed bound.  Here φ/2 = 1/6, corresponding to φ = 1/3.
-/
theorem F1_neg_lam (K lam : ℝ) (hK : 0 < K) (hlam : 0 < lam) :
    Work.LinnikAreas.A5.F1 K lam (-(lam:ℂ)) =
      ((Real.exp (K*lam) * (K/2 - (1 - Real.exp (-2*K*lam))/(4*lam)) : ℝ) : ℂ) ∧
    (2/lam) * Real.exp (-(K*lam)) *
        (Real.sinh (K*lam)/6 + Real.exp (K*lam) * (K/2 - (1 - Real.exp (-2*K*lam))/(4*lam)))
      = K^2 * Work.LinnikContract.Bfun K lam := by
  constructor
  · -- (i): the Laplace transform at `z = -λ` is the elementary integral computed above.
    rw [F1_eq_integral hK.le]
    rw [show (∫ t in (0:ℝ)..K,
            Complex.exp (-(-(lam:ℂ) * (t:ℂ))) * ((Real.sinh ((K-t)*lam) : ℝ) : ℂ))
        = ∫ t in (0:ℝ)..K, ((Real.exp (lam*t) * Real.sinh ((K-t)*lam) : ℝ) : ℂ) from by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [show -(-(lam:ℂ) * (t:ℂ)) = ((lam*t : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_exp, ← Complex.ofReal_mul]]
    rw [intervalIntegral.integral_ofReal, integral_exp_mul_sinh K lam hlam]
  · -- (ii): expand `sinh(Kλ)`, clear denominators and reduce to a polynomial identity.
    rw [Work.LinnikContract.Bfun, if_neg (ne_of_gt hlam), Real.sinh_eq]
    have hE : Real.exp (K*lam) ≠ 0 := (Real.exp_pos _).ne'
    have hneg : Real.exp (-(K*lam)) = (Real.exp (K*lam))⁻¹ := Real.exp_neg _
    have hneg2 : Real.exp (-2*K*lam) = (Real.exp (K*lam)^2)⁻¹ := by
      rw [show -2*K*lam = -(((2:ℕ) : ℝ) * (K*lam)) by ring, Real.exp_neg, Real.exp_nat_mul]
    rw [hneg, hneg2]
    field_simp
    ring

end Work.LinnikAreas.A5
