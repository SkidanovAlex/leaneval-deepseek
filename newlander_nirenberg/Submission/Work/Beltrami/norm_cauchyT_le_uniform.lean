import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.norm_cauchyT_le

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff
open Work.Beltrami

noncomputable section

/-- **Uniform potential bound for the Cauchy transform.**  There is a constant `C` such that for
every continuous `f` bounded by `M` and supported in the disc of radius `R ≥ 0`, the Cauchy
potential satisfies `‖cauchyT f z‖ ≤ C * M * (1 + R)` for all `z`, with `C` independent of
`f`, `M` and `R`. -/
theorem norm_cauchyT_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (M R : ℝ), Continuous f → 0 ≤ R →
      (∀ z, ‖f z‖ ≤ M) → (∀ z, R < ‖z‖ → f z = 0) →
      ∀ z, ‖cauchyT f z‖ ≤ C * M * (1 + R) := by
  classical
  refine ⟨6, by norm_num, ?_⟩
  intro f M R hf hR hM hsupp z
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  have hstep1 : ‖cauchyT f z‖ = (Real.pi)⁻¹ * ‖∫ ζ, (ζ - z)⁻¹ * f ζ ∂volume‖ := by
    rw [cauchyT_apply, norm_smul]
    congr 1
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (inv_nonneg.mpr Real.pi_pos.le)]
  have hle : ∀ ζ : ℂ, ‖(ζ - z)⁻¹ * f ζ‖ ≤
      M * (Metric.ball (0:ℂ) (R+1)).indicator (fun ζ => ‖ζ - z‖⁻¹) ζ := by
    intro ζ
    by_cases h : ζ ∈ Metric.ball (0:ℂ) (R+1)
    · rw [Set.indicator_of_mem h]
      rw [show ‖(ζ - z)⁻¹ * f ζ‖ = ‖f ζ‖ * ‖ζ - z‖⁻¹ from by
        rw [norm_mul, norm_inv, mul_comm]]
      exact mul_le_mul_of_nonneg_right (hM ζ) (inv_nonneg.mpr (norm_nonneg _))
    · rw [Set.indicator_of_notMem h]
      have hf0 : f ζ = 0 := hsupp ζ (by
        rw [Metric.mem_ball, not_lt, dist_eq_norm] at h
        have : R + 1 ≤ ‖ζ‖ := by simpa [sub_zero] using h
        linarith)
      simp [hf0]
  have hint : Integrable
      (fun ζ : ℂ => M * (Metric.ball (0:ℂ) (R+1)).indicator (fun ζ => ‖ζ - z‖⁻¹) ζ) :=
    (integrable_indicator_norm_sub_inv z (R+1)).const_mul M
  have hJ0 := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ζ => norm_nonneg _))
    hint (Filter.Eventually.of_forall hle)
  rw [integral_const_mul] at hJ0
  rw [integral_indicator Metric.isOpen_ball.measurableSet] at hJ0
  have hJ : ∫ ζ, ‖(ζ - z)⁻¹ * f ζ‖ ∂volume ≤ M * (6 * Real.pi * (1 + R)) := by
    have hp := integral_ball_norm_sub_inv_le z R hR
    nlinarith [hJ0, mul_le_mul_of_nonneg_left hp hM0]
  rw [hstep1]
  calc (Real.pi)⁻¹ * ‖∫ ζ, (ζ - z)⁻¹ * f ζ ∂volume‖
      ≤ (Real.pi)⁻¹ * ∫ ζ, ‖(ζ - z)⁻¹ * f ζ‖ ∂volume :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
          (inv_nonneg.mpr Real.pi_pos.le)
    _ ≤ (Real.pi)⁻¹ * (M * (6 * Real.pi * (1 + R))) :=
        mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr Real.pi_pos.le)
    _ = 6 * M * (1 + R) := by
        have hp : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp

end

end Work.Beltrami
