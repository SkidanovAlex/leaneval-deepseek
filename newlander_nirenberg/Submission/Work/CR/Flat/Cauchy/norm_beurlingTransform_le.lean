import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- Pointwise bound for the Beurling transform
`beurlingTransform ρ f z = -(1/π) ∫_{‖w‖<ρ} (f (z+w) - f z)/w^2` of
`Submission/Work/CR/Flat/Cauchy.lean`.

For `f` `α`-Hölder with constant `C` (`0 < α`),
`‖S f z‖ ≤ C ∫_{‖w‖<ρ} ‖w‖^{α-2} = 2 C ρ^α/α`; the subtraction makes the
integral converge since `α - 2 > -2`.  No support condition is needed. -/
theorem norm_beurlingTransform_le {ρ α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) {z : ℂ} (hz : ‖z‖ < ρ) :
    ‖beurlingTransform ρ f z‖ ≤ 2 * C * ρ ^ α / α := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hz
  -- pointwise bound on the integrand by the (locally integrable) majorant
  have hpt : ∀ w : ℂ, ‖(f (z + w) - f z) / w ^ 2‖ ≤ C * ‖w‖ ^ (α - 2) := by
    intro w
    by_cases hw : w = 0
    · have hzero : ‖(f (z + w) - f z) / w ^ 2‖ = 0 := by rw [hw]; simp
      rcases eq_or_ne (α - 2) 0 with ha | ha
      · rw [hzero, hw, norm_zero, ha, Real.rpow_zero, mul_one]
        exact hC
      · rw [hzero, hw, norm_zero, Real.zero_rpow ha, mul_zero]
    · have hfw : ‖f (z + w) - f z‖ ≤ C * ‖w‖ ^ α := by
        have h := hf (z + w) z
        rwa [add_sub_cancel_left] at h
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      -- write the kernel `‖w‖^2` (a natural power) as a real power of `‖w‖`
      have h2 : ‖w‖ ^ (2 : ℝ) = ‖w‖ ^ 2 := Real.rpow_natCast ‖w‖ 2
      rw [norm_div, norm_pow, ← h2]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖w‖ ^ (2 : ℝ))]
      have hkey : C * ‖w‖ ^ (α - 2) * ‖w‖ ^ (2 : ℝ) = C * ‖w‖ ^ α := by
        rw [mul_assoc, ← Real.rpow_add hwpos (α - 2) 2,
          show α - 2 + 2 = α from by ring]
      rw [hkey]
      exact hfw
  -- the majorant is integrable on the disc
  have hInt : IntegrableOn (fun w : ℂ => C * ‖w‖ ^ (α - 2)) (Metric.ball 0 ρ) volume :=
    (integrableOn_norm_rpow_ball (ρ := ρ) (s := α - 2) (by linarith)).const_mul C
  have hbound : ‖∫ w in Metric.ball 0 ρ, (f (z + w) - f z) / w ^ 2‖
      ≤ ∫ w : ℂ in Metric.ball 0 ρ, C * ‖w‖ ^ (α - 2) :=
    MeasureTheory.norm_integral_le_of_norm_le hInt (Filter.Eventually.of_forall hpt)
  -- evaluate the majorant integral: `∫_{‖w‖<ρ} ‖w‖^{α-2} = 2πρ^α/α`
  have hval : (∫ w : ℂ in Metric.ball 0 ρ, C * ‖w‖ ^ (α - 2))
      = 2 * Real.pi * C * ρ ^ α / α := by
    rw [integral_const_mul, integral_norm_rpow_ball hρ (by linarith : -2 < α - 2),
      show (α - 2) + 2 = α from by ring]
    ring
  have hpi2 : Real.pi⁻¹ * (2 * Real.pi) = 2 := by
    rw [mul_comm (2 : ℝ) Real.pi, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  calc ‖beurlingTransform ρ f z‖
      = ‖((Real.pi : ℂ))⁻¹‖ * ‖∫ w in Metric.ball 0 ρ, (f (z + w) - f z) / w ^ 2‖ := by
        simp only [beurlingTransform, norm_mul, norm_neg]
    _ ≤ Real.pi⁻¹ * (∫ w : ℂ in Metric.ball 0 ρ, C * ‖w‖ ^ (α - 2)) := by
        rw [show ‖((Real.pi : ℂ))⁻¹‖ = Real.pi⁻¹ by
          rw [norm_inv]; simp [Real.norm_of_nonneg Real.pi_pos.le]]
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 2 * C * ρ ^ α / α := by
        rw [hval,
          show Real.pi⁻¹ * (2 * Real.pi * C * ρ ^ α / α)
              = (Real.pi⁻¹ * (2 * Real.pi)) * (C * ρ ^ α / α) by ring,
          hpi2]
        ring

end Work.CR.Flat.Cauchy
