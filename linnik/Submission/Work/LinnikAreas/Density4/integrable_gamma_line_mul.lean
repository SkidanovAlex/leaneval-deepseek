import Mathlib
import Submission.Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp
import Submission.Work.LinnikAreas.Density4.gamma_vertical_integrable_of_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay

namespace Work.LinnikAreas.Density4

open MeasureTheory

/-- The function `t ↦ ‖Γ (a + i t)‖ * (2 + |t|)` is integrable for every `a > 0`.

The uniform Stirling-type estimate `gamma_vertical_exp_decay` bounds `‖Γ (a + i t)‖` by
`C * (1 + |t|) ^ a * exp (-(π / 2) * |t|)`; multiplying by `2 + |t| ≤ 3 * (1 + |t|)` and
absorbing the extra power of `(1 + |t|)` into the exponent gives the integrable majorant
`3 * C * (1 + |t|) ^ (a + 1) * exp (-(π / 2) * |t|)` of `integrable_one_add_abs_rpow_exp`. -/
theorem integrable_gamma_line_mul (a : ℝ) (ha : 0 < a) :
    MeasureTheory.Integrable (fun t : ℝ => ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay a ha
  have hGint : Integrable
      (fun t : ℝ => (1 + |t|) ^ (a + 1) * Real.exp (-(Real.pi / 2 * |t|))) :=
    integrable_one_add_abs_rpow_exp (a + 1) (Real.pi / 2) (by positivity)
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)) := by
    have h1 : Measurable (fun t : ℝ => ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖) :=
      (measurable_gamma_vertical a).norm
    exact (h1.mul (measurable_const.add continuous_abs.measurable)).aestronglyMeasurable
  refine (hGint.const_mul (3 * C)).mono' hmeas ?_
  filter_upwards with t
  have ht1 : (0 : ℝ) < 1 + |t| := by linarith [abs_nonneg t]
  have h1 : ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C * (1 + |t|) ^ a * Real.exp (-(Real.pi / 2 * |t|)) := by
    have hh := hC t
    rw [mul_comm Complex.I (t : ℂ), show -(Real.pi / 2) * |t| = -(Real.pi / 2 * |t|) by ring] at hh
    exact hh
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by linarith [abs_nonneg t]))]
  have h2 : (2 + |t|) ≤ 3 * (1 + |t|) := by linarith [abs_nonneg t]
  have hpow : (1 + |t|) ^ (a + 1) = (1 + |t|) ^ a * (1 + |t|) :=
    Real.rpow_add_one ht1.ne' a
  calc ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)
      ≤ (C * (1 + |t|) ^ a * Real.exp (-(Real.pi / 2 * |t|))) * (3 * (1 + |t|)) :=
        mul_le_mul h1 h2 (by linarith [abs_nonneg t]) (by positivity)
    _ = 3 * C * ((1 + |t|) ^ (a + 1) * Real.exp (-(Real.pi / 2 * |t|))) := by
        rw [hpow]; ring

end Work.LinnikAreas.Density4
