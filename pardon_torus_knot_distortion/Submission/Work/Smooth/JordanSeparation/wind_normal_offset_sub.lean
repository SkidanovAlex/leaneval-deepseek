import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

namespace Work.Smooth.JordanSeparation

open Set intervalIntegral MeasureTheory
open Work.Smooth.Jordan

/-- The purely algebraic core of `wind_normal_offset_sub`: for two complex points
`z ± s·N`, the difference of the corresponding `1`-form integrands is a single fraction whose
denominator is `(z - z0)² + s²T²` whenever `N = I·T`. -/
private theorem div_sub_div_normal (z z0 T N g : ℂ) (s : ℂ) (hN : N = Complex.I * T)
    (hzp : z - (z0 + s * N) ≠ 0) (hzm : z - (z0 - s * N) ≠ 0)
    (hpi : (Real.pi : ℂ) ≠ 0) (hD : (z - z0) ^ 2 + s ^ 2 * T ^ 2 ≠ 0) :
    g / (z - (z0 + s * N)) - g / (z - (z0 - s * N))
      = (2 * (Real.pi : ℂ) * Complex.I) *
          ((1 / (Real.pi : ℂ)) * T * (s * g / ((z - z0) ^ 2 + s ^ 2 * T ^ 2))) := by
  subst hN
  have hden : (z - (z0 + s * (Complex.I * T))) * (z - (z0 - s * (Complex.I * T)))
      = (z - z0) ^ 2 + s ^ 2 * T ^ 2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [div_sub_div (b := z - (z0 + s * (Complex.I * T)))
        (d := z - (z0 - s * (Complex.I * T))) g g hzp hzm, hden]
  field_simp
  ring

theorem wind_normal_offset_sub (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (h : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c) {s : ℝ} (hs : 0 < s)
    (hspos : c.γ 0 + s * Work.Smooth.JordanSeparation.normalField c 0 ∉ c.trace)
    (hsneg : c.γ 0 - s * Work.Smooth.JordanSeparation.normalField c 0 ∉ c.trace) :
    Work.Smooth.Jordan.wind c (c.γ 0 + s * Work.Smooth.JordanSeparation.normalField c 0)
        - Work.Smooth.Jordan.wind c (c.γ 0 - s * Work.Smooth.JordanSeparation.normalField c 0)
      = (1 / (Real.pi : ℂ)) * Work.Smooth.JordanSeparation.unitTangent c 0 *
        (∫ τ in (0 : ℝ)..(2 * Real.pi),
          (s * deriv c.γ τ) /
            ((c.γ τ - c.γ 0) ^ 2
              + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Work.Smooth.Jordan.two_pi_I_ne_zero
  have hintp : IntervalIntegrable (windingIntegrand c (c.γ 0 + s * normalField c 0)) volume 0
      (2 * Real.pi) :=
    (Work.Smooth.Jordan.continuous_windingIntegrand c hspos).intervalIntegrable _ _
  have hintm : IntervalIntegrable (windingIntegrand c (c.γ 0 - s * normalField c 0)) volume 0
      (2 * Real.pi) :=
    (Work.Smooth.Jordan.continuous_windingIntegrand c hsneg).intervalIntegrable _ _
  have hpoint : ∀ τ : ℝ,
      windingIntegrand c (c.γ 0 + s * normalField c 0) τ
        - windingIntegrand c (c.γ 0 - s * normalField c 0) τ
      = (2 * (Real.pi : ℂ) * Complex.I) *
          ((1 / (Real.pi : ℂ)) * unitTangent c 0 *
            (s * deriv c.γ τ /
              ((c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2))) := by
    intro τ
    have hzp : c.γ τ - (c.γ 0 + (s : ℂ) * normalField c 0) ≠ 0 := by
      intro hh
      apply hspos
      rw [← sub_eq_zero.mp hh]
      exact c.mem_trace τ
    have hzm : c.γ τ - (c.γ 0 - (s : ℂ) * normalField c 0) ≠ 0 := by
      intro hh
      apply hsneg
      rw [← sub_eq_zero.mp hh]
      exact c.mem_trace τ
    have hden : (c.γ τ - (c.γ 0 + (s : ℂ) * normalField c 0))
        * (c.γ τ - (c.γ 0 - (s : ℂ) * normalField c 0))
        = (c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2 := by
      rw [normalField_def]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hD : (c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2 ≠ 0 := by
      rw [← hden]
      exact mul_ne_zero hzp hzm
    rw [windingIntegrand_apply, windingIntegrand_apply]
    exact div_sub_div_normal (c.γ τ) (c.γ 0) (unitTangent c 0) (normalField c 0)
      (deriv c.γ τ) (s : ℂ) (normalField_def c 0) hzp hzm hpi hD
  rw [wind_def, wind_def, windingPrimitive, windingPrimitive, ← mul_sub]
  rw [← intervalIntegral.integral_sub hintp hintm]
  rw [intervalIntegral.integral_congr (fun τ _ => hpoint τ)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [← mul_assoc, inv_mul_cancel₀ h2piI, one_mul]

end Work.Smooth.JordanSeparation
