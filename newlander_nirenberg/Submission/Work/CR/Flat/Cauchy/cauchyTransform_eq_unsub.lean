import Mathlib
import Submission.Work.CR.Flat.Cauchy

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- The Cauchy kernel `w ↦ w⁻¹` is locally integrable on `ℂ`: it is dominated by
`‖w‖ ^ (-1)` and `1 < finrank ℝ ℂ = 2`. -/
theorem locallyIntegrable_inv_complex :
    LocallyIntegrable (fun w : ℂ => w⁻¹) (volume : Measure ℂ) := by
  refine locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ) (μ := (volume : Measure ℂ))
    (C := 1) (α := 1)
    (le_of_lt (by rw [Complex.finrank_real_complex]; norm_num))
    (by rw [Complex.finrank_real_complex]; norm_num) ?_ measurable_inv.aestronglyMeasurable
  filter_upwards with x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [norm_inv, Real.rpow_neg_one]
    simp

/-- The Cauchy kernel is integrable on every disc `‖w‖ < ρ` (the singularity
`‖w‖⁻¹` is integrable in the plane, `∫_{‖w‖<ρ} ‖w‖⁻¹ = 2πρ`). -/
theorem integrableOn_inv_ball (ρ : ℝ) :
    IntegrableOn (fun w : ℂ => w⁻¹) (Metric.ball 0 ρ) :=
  (locallyIntegrable_inv_complex.integrableOn_isCompact (isCompact_closedBall 0 ρ)).mono_set
    Metric.ball_subset_closedBall

/-- The Cauchy potential of `Submission/Work/CR/Flat/Cauchy.lean` agrees with the
"unsubtracted" integral, whenever the latter converges absolutely.

Indeed `∫_{‖w‖<ρ} (f (z+w) - f z)/w = ∫_{‖w‖<ρ} f (z+w)/w - f z · ∫_{‖w‖<ρ} 1/w`
and the last factor vanishes by the symmetry `w ↔ -w` (`integral_inv_ball`).
This is what lets one differentiate the potential with respect to `z` under the
integral sign over the *fixed* disc `‖w‖ < ρ`. -/
theorem cauchyTransform_eq_unsub {ρ : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (hf : IntegrableOn (fun w : ℂ => f (z + w) / w) (Metric.ball 0 ρ)) :
    cauchyTransform ρ f z = cauchyTransformUnsub ρ f z := by
  -- `w ↦ f z / w` is the constant `f z` times the integrable kernel `w ↦ w⁻¹`
  have hcint : IntegrableOn (fun w : ℂ => f z / w) (Metric.ball 0 ρ) := by
    have h : (fun w : ℂ => f z / w) = fun w : ℂ => f z * w⁻¹ := by
      funext w; rw [div_eq_mul_inv]
    rw [h]
    exact (integrableOn_inv_ball ρ).const_mul (f z)
  -- and its integral vanishes by the symmetry `w ↔ -w`
  have hc0 : ∫ w in Metric.ball (0 : ℂ) ρ, f z / w = 0 := by
    have h : (fun w : ℂ => f z / w) = fun w : ℂ => f z * w⁻¹ := by
      funext w; rw [div_eq_mul_inv]
    rw [h, integral_const_mul, integral_inv_ball ρ, mul_zero]
  -- split the subtracted integrand
  have hsplit : ∫ w in Metric.ball (0 : ℂ) ρ, (f (z + w) - f z) / w
      = (∫ w in Metric.ball (0 : ℂ) ρ, f (z + w) / w)
        - ∫ w in Metric.ball (0 : ℂ) ρ, f z / w := by
    have h : (fun w : ℂ => (f (z + w) - f z) / w)
        = fun w : ℂ => f (z + w) / w - f z / w := by
      funext w; rw [sub_div]
    rw [h]
    exact integral_sub hf hcint
  simp only [cauchyTransform, cauchyTransformUnsub]
  rw [hsplit, hc0, sub_zero]

end Work.CR.Flat.Cauchy
