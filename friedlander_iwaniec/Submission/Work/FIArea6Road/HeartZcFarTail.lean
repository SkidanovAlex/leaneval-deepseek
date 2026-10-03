import Mathlib
import Submission.Work.FIArea6Road.HeartFarIntegral
import Submission.Work.FIArea6Road.FarTailIntegrable

namespace Work.FIArea6Road

open MeasureTheory

theorem HeartZcFarTail :
    ∃ K : ℝ, 0 < K ∧
      ∀ (F : ℝ → ℂ) (θ T M Kz : ℝ), 0 < θ → 1 ≤ T → 0 ≤ M → 0 ≤ Kz →
        MeasureTheory.IntegrableOn
          (fun t : ℝ => (1 + (θ * t) ^ 2)⁻¹ * (M + Real.log (1 + |t|)) ^ (6 : ℕ))
          (Set.Ioi T ∪ Set.Iio (-T)) →
        (∀ t : ℝ, T < |t| →
          ‖F t‖ ≤ Kz * ((1 + (θ * t) ^ 2)⁻¹ * (M + Real.log (1 + |t|)) ^ (6 : ℕ))) →
        (∫ t in Set.Ioi T, ‖F t‖) + (∫ t in Set.Iio (-T), ‖F t‖)
          ≤ K * Kz / (θ ^ 2 * T) * (M + Real.log (2 * T) + 1) ^ (6 : ℕ) := by
  obtain ⟨K0, hK0pos, hK0⟩ := HeartFarIntegral
  refine ⟨2 * K0, by positivity, ?_⟩
  intro F θ T M Kz hθ hT1 hM hKz hint hbound
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  set φ : ℝ → ℝ :=
    fun t => (1 + (θ * t) ^ 2)⁻¹ * (M + Real.log (1 + |t|)) ^ (6 : ℕ) with hφdef
  have hφpos : IntegrableOn φ (Set.Ioi T) := hint.mono_set Set.subset_union_left
  have hφneg : IntegrableOn φ (Set.Iio (-T)) := hint.mono_set Set.subset_union_right
  -- comparison on the positive tail
  have hcmp_pos : (∫ t in Set.Ioi T, ‖F t‖) ≤ ∫ t in Set.Ioi T, Kz * φ t := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun t => norm_nonneg (F t))
    · exact Integrable.const_mul hφpos Kz
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Set.mem_Ioi] at ht
      exact hbound t (by rw [abs_of_pos (lt_trans hTpos ht)]; exact ht)
  -- comparison on the negative tail
  have hcmp_neg : (∫ t in Set.Iio (-T), ‖F t‖) ≤ ∫ t in Set.Iio (-T), Kz * φ t := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun t => norm_nonneg (F t))
    · exact Integrable.const_mul hφneg Kz
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iio] with t ht
      rw [Set.mem_Iio] at ht
      have htneg : t < 0 := lt_trans ht (by linarith)
      exact hbound t (by rw [abs_of_neg htneg]; linarith)
  -- identify the weight on the positive tail with the form used by `HeartFarIntegral`
  have hφIoi : (∫ t in Set.Ioi T, φ t)
      = ∫ t in Set.Ioi T, (1 + (θ * t) ^ 2)⁻¹ * (M + Real.log (t + 1)) ^ (6 : ℕ) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [hφdef]
    rw [Set.mem_Ioi] at ht
    have ht0 : 0 < t := lt_trans hTpos ht
    rw [abs_of_pos ht0, show (1 : ℝ) + t = t + 1 by ring]
  have hφbound : (∫ t in Set.Ioi T, φ t)
      ≤ K0 / (θ ^ 2 * T) * (M + Real.log (2 * T) + 1) ^ (6 : ℕ) := by
    rw [hφIoi]
    exact hK0 θ T M 1 hθ le_rfl hT1 hT1 hM
  -- the weight is even, so the negative tail has the same integral
  have hφneg_eq : (∫ t in Set.Iio (-T), φ t) = ∫ t in Set.Ioi T, φ t := by
    calc ∫ t in Set.Iio (-T), φ t
        = ∫ t in Set.Iic (-T), φ t :=
          (integral_Iic_eq_integral_Iio (x := -T) (f := φ)).symm
      _ = ∫ t in Set.Iic (-T), φ (-t) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
          intro t _
          simp only [hφdef]
          rw [abs_neg]
          rw [show (θ * (-t)) ^ 2 = (θ * t) ^ 2 by ring]
      _ = ∫ t in Set.Ioi T, φ t := by
          have h := integral_comp_neg_Iic (-T) φ
          rw [neg_neg] at h
          exact h
  have hsum : (∫ t in Set.Ioi T, φ t) + (∫ t in Set.Iio (-T), φ t)
      ≤ 2 * (K0 / (θ ^ 2 * T) * (M + Real.log (2 * T) + 1) ^ (6 : ℕ)) := by
    rw [hφneg_eq]
    linarith [hφbound]
  calc (∫ t in Set.Ioi T, ‖F t‖) + (∫ t in Set.Iio (-T), ‖F t‖)
      ≤ (∫ t in Set.Ioi T, Kz * φ t) + (∫ t in Set.Iio (-T), Kz * φ t) :=
        add_le_add hcmp_pos hcmp_neg
    _ = Kz * (∫ t in Set.Ioi T, φ t) + Kz * (∫ t in Set.Iio (-T), φ t) := by
        rw [integral_const_mul, integral_const_mul]
    _ = Kz * ((∫ t in Set.Ioi T, φ t) + (∫ t in Set.Iio (-T), φ t)) := by ring
    _ ≤ Kz * (2 * (K0 / (θ ^ 2 * T) * (M + Real.log (2 * T) + 1) ^ (6 : ℕ))) :=
        mul_le_mul_of_nonneg_left hsum hKz
    _ = (2 * K0) * Kz / (θ ^ 2 * T) * (M + Real.log (2 * T) + 1) ^ (6 : ℕ) := by ring

end Work.FIArea6Road
