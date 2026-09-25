import Mathlib
import Submission.Commons.Analysis.Oscillatory.van_der_corput_bound
import Submission.Commons.Analysis.Oscillatory.integral_quadratic_phase_le

namespace Commons.Analysis.Fresnel

open MeasureTheory
open scoped BigOperators ENNReal Topology

/-- Bourgain (5.19) for the quadratic phase: the Fresnel integral `∫₀¹ e(x s²) ds` decays like
`|x|^{-1/2}`.  Proved from `Commons.Analysis.Oscillatory.van_der_corput_bound` with `k = 2`
(the second derivative of the phase `2πx s²` is the constant `4πx`). -/
theorem fresnel_integral_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ))‖
        ≤ C / Real.sqrt |x| := by
  refine ⟨8, by norm_num, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hx
    norm_num at hx
  have hcongr : (∫ s in (0:ℝ)..1,
        Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)))
      = ∫ s in (0:ℝ)..1,
        Complex.exp (((2 * Real.pi * (x * s ^ 2 + 0 * s) : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro s _
    show Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ))
        = Complex.exp (((2 * Real.pi * (x * s ^ 2 + 0 * s) : ℝ) : ℂ) * Complex.I)
    congr 1
    push_cast
    ring
  rw [hcongr]
  exact Commons.Analysis.Oscillatory.integral_quadratic_phase_le x 0 0 1 hx0

end Commons.Analysis.Fresnel
