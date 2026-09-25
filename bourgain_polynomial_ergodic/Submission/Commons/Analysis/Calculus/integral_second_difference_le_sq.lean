import Mathlib
import Submission.Commons.Analysis.Calculus.integral_second_difference_le
import Submission.Commons.MeasureTheory.Integral.double_window_comp_add_add

open MeasureTheory Set

namespace Commons.Analysis.Calculus

/-- **Second-difference `L¹` estimate (sharp constant).** For `h ≥ 0` and a twice
differentiable `m : ℝ → ℂ` with integrable second derivative,
`∫ x, ‖m x - 2 m (x+h) + m (x+2h)‖ ≤ h² ∫ x, ‖m'' x‖`.

This is the sharp form of `integral_second_difference_le`: the pointwise bound
`ofReal_norm_second_difference_le` expresses the second difference through the double window
integral `∫⁻ t in (0,h], ∫⁻ s in (0,h], ‖m'' (x+t+s)‖`, whose total mass is exactly `h²`
(by `double_window_comp_add_add`). -/
theorem integral_second_difference_le_sq (m : ℝ → ℂ) (h : ℝ) (hh : 0 ≤ h)
    (hd1 : Differentiable ℝ m) (hd2 : Differentiable ℝ (deriv m))
    (hint2 : MeasureTheory.Integrable (deriv (deriv m))) :
    ∫ x, ‖m x - 2 * m (x + h) + m (x + 2 * h)‖
      ≤ h ^ 2 * ∫ x, ‖deriv (deriv m) x‖ := by
  classical
  let A : ℝ → ℂ := fun x => m x - 2 * m (x + h) + m (x + 2 * h)
  let F : ℝ → ENNReal := fun y => ENNReal.ofReal ‖deriv (deriv m) y‖
  change ∫ x, ‖A x‖ ≤ h ^ 2 * ∫ x, ‖deriv (deriv m) x‖
  have hFmeas : Measurable F :=
    ENNReal.measurable_ofReal.comp (measurable_deriv (deriv m)).norm
  have hcontA : Continuous A := by
    refine ((hd1.continuous.sub (continuous_const.mul
      (hd1.continuous.comp (continuous_id.add continuous_const)))).add ?_)
    exact hd1.continuous.comp (continuous_id.add continuous_const)
  have hpt : ∀ x, ENNReal.ofReal ‖A x‖
      ≤ ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h, F (x + t + s) :=
    fun x => ofReal_norm_second_difference_le m h x hh hd1 hd2 hint2
  have hstep1 : ENNReal.ofReal (∫ x, ‖A x‖) ≤ ∫⁻ x, ENNReal.ofReal ‖A x‖ := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => norm_nonneg _)
      hcontA.norm.aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  have hstep2 : ∫⁻ x, ENNReal.ofReal ‖A x‖
      ≤ ∫⁻ x, ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h, F (x + t + s) :=
    lintegral_mono hpt
  have hwin : ∫⁻ x, ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h, F (x + t + s)
      = ENNReal.ofReal h * (ENNReal.ofReal h * ∫⁻ x, F x) :=
    Commons.MeasureTheory.Integral.double_window_comp_add_add hh hFmeas
  have hFin : ∫⁻ x, F x = ENNReal.ofReal (∫ x, ‖deriv (deriv m) x‖) :=
    (ofReal_integral_eq_lintegral_ofReal hint2.norm (ae_of_all _ fun x => norm_nonneg _)).symm
  have hchain : ENNReal.ofReal (∫ x, ‖A x‖)
      ≤ ENNReal.ofReal (h ^ 2 * ∫ x, ‖deriv (deriv m) x‖) := by
    calc ENNReal.ofReal (∫ x, ‖A x‖) ≤ ∫⁻ x, ENNReal.ofReal ‖A x‖ := hstep1
      _ ≤ ∫⁻ x, ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h, F (x + t + s) := hstep2
      _ = ENNReal.ofReal h * (ENNReal.ofReal h * ∫⁻ x, F x) := hwin
      _ = ENNReal.ofReal h
            * (ENNReal.ofReal h * ENNReal.ofReal (∫ x, ‖deriv (deriv m) x‖)) := by
            rw [hFin]
      _ = ENNReal.ofReal (h ^ 2 * ∫ x, ‖deriv (deriv m) x‖) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hh, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
  have hI2nn : 0 ≤ ∫ x, ‖deriv (deriv m) x‖ := integral_nonneg (fun x => norm_nonneg _)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg h) hI2nn)).mp hchain

end Commons.Analysis.Calculus
