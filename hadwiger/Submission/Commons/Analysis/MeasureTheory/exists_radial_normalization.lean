import Mathlib
import Submission.Commons.Analysis.MeasureTheory.integral_radial_mul_homogeneous

open MeasureTheory Set
open scoped Classical

noncomputable section

namespace Commons.Analysis.MeasureTheory

/-- The integral against `Measure.volumeIoiPow m` of a product `r * φ r`, rewritten as a
Lebesgue integral of `r^(m+1) * φ r` over `(0, ∞)`. -/
private lemma volumeIoiPow_integral_mul (m : ℕ) (φ : ℝ → ℝ) :
    ∫ r : Set.Ioi (0:ℝ), (r:ℝ) * φ r ∂(Measure.volumeIoiPow m)
      = ∫ r in Set.Ioi (0:ℝ), r^(m+1) * φ r := by
  rw [integral_volumeIoiPow_eq_integral_Ioi_mul_pow m (fun r => r * φ r)]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  change x ^ m * (x * φ x) = x ^ (m+1) * φ x
  rw [pow_succ]; ring

/-- Integral of `r^{m+1}` against the tent function `r ↦ max r 0 * max (1-r) 0`. -/
private lemma tent_integral (m : ℕ) :
    ∫ r in Set.Ioi (0:ℝ), r^(m+1) * (max r 0 * max (1-r) 0)
      = 1/(((m:ℝ)+3)*((m:ℝ)+4)) := by
  calc
    ∫ r in Set.Ioi (0:ℝ), r^(m+1) * (max r 0 * max (1-r) 0)
        = ∫ r in Set.Ioc (0:ℝ) 1, r^(m+1) * (max r 0 * max (1-r) 0) := by
          refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
            (fun x hx => hx.1) (fun x hx => ?_)
          rw [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and_or] at hx
          obtain ⟨hx1, hx2⟩ := hx
          have hxgt : 1 < x := by
            rcases hx2 with h | h
            · exact absurd hx1 h
            · linarith
          have hh : max (1-x) 0 = 0 := max_eq_right (by linarith)
          rw [hh]; ring
    _ = ∫ r in Set.Ioc (0:ℝ) 1, r^(m+2) * (1 - r) := by
          refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
          have hr : max x 0 = x := max_eq_left (le_of_lt hx.1)
          have h1r : max (1-x) 0 = 1-x := max_eq_left (by linarith [hx.2])
          rw [hr, h1r, ← mul_assoc, ← pow_succ]
    _ = ∫ r in (0:ℝ)..1, r^(m+2) * (1 - r) := by
          rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    _ = 1/(((m:ℝ)+3)*((m:ℝ)+4)) := by
          have h1 : ∀ r : ℝ, r^(m+2) * (1 - r) = r^(m+2) - r^(m+3) := by
            intro r; rw [mul_sub, mul_one, ← pow_succ]
          rw [intervalIntegral.integral_congr (fun r _ => h1 r)]
          rw [intervalIntegral.integral_sub]
          · rw [integral_pow, integral_pow]
            push_cast
            norm_num
            field_simp
            ring
          · exact (continuous_id.pow _).intervalIntegrable _ _
          · exact (continuous_id.pow _).intervalIntegrable _ _

theorem exists_radial_normalization (m : ℕ) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ φ 0 = 0 ∧
      (∫ r : Set.Ioi (0 : ℝ), (r : ℝ) * φ r ∂(MeasureTheory.Measure.volumeIoiPow m)) = 1 := by
  refine ⟨fun r => (((m:ℝ)+3)*((m:ℝ)+4)) * (max r 0 * max (1-r) 0), ?_, ?_, ?_, ?_⟩
  · apply Continuous.const_mul
    apply Continuous.mul
    · exact continuous_id.max continuous_const
    · exact (continuous_const.sub continuous_id).max continuous_const
  · apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro r hr
    rw [Function.mem_support] at hr
    rw [mem_Icc]
    constructor
    · by_contra h
      have hlt : r < 0 := not_le.mp h
      have hz : max r 0 = 0 := max_eq_right (le_of_lt hlt)
      simp [hz] at hr
    · by_contra h
      have hlt : 1 < r := not_le.mp h
      have hz : max (1-r) 0 = 0 := max_eq_right (by linarith)
      simp [hz] at hr
  · norm_num
  · rw [volumeIoiPow_integral_mul m (fun r => (((m:ℝ)+3)*((m:ℝ)+4)) * (max r 0 * max (1-r) 0))]
    rw [show ∫ r in Set.Ioi (0:ℝ), r^(m+1) * (((m:ℝ)+3)*((m:ℝ)+4) * (max r 0 * max (1-r) 0))
        = ∫ r in Set.Ioi (0:ℝ), (((m:ℝ)+3)*((m:ℝ)+4)) * (r^(m+1) * (max r 0 * max (1-r) 0)) from by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx; ring]
    rw [integral_const_mul, tent_integral m]
    have hc : (((m:ℝ)+3)*((m:ℝ)+4)) ≠ 0 := by positivity
    field_simp

end Commons.Analysis.MeasureTheory

