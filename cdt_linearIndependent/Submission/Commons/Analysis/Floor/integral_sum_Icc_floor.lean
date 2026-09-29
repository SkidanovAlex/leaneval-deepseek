import Mathlib
import Submission.Commons.Analysis.Floor.sum_Icc_floor_eq
import Submission.Commons.MeasureTheory.IntervalIntegral.integral_indicator_Ici

namespace Commons.Analysis.Floor

open _root_.MeasureTheory

theorem integral_sum_Icc_floor (c : ℕ → ℝ) {B : ℝ} (hB : 0 < B) {v : ℝ} (hv : 1 ≤ v) :
    (∫ t in 1..v, ∑ h ∈ Finset.Icc 1 ⌊(t - 1) / B⌋₊, c h)
      = ∑ h ∈ Finset.Icc 1 ⌊(v - 1) / B⌋₊, c h * max (v - max 1 (1 + h * B)) 0 := by
  set N := ⌊(v - 1) / B⌋₊ with hN
  have hcongr : Set.EqOn (fun t : ℝ => ∑ h ∈ Finset.Icc 1 ⌊(t - 1) / B⌋₊, c h)
      (fun t : ℝ => ∑ h ∈ Finset.Icc 1 N, c h * (if 1 + (h:ℝ) * B ≤ t then (1:ℝ) else 0))
      (Set.uIcc 1 v) := by
    rw [Set.uIcc_of_le hv]
    intro t ht
    rw [Set.mem_Icc] at ht
    obtain ⟨ht1, htv⟩ := ht
    have hA : (0:ℝ) ≤ (t - 1) / B := div_nonneg (by linarith) hB.le
    have hH : ⌊(t - 1) / B⌋₊ ≤ N := by
      rw [hN]
      exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hB.le)
    change (∑ h ∈ Finset.Icc 1 ⌊(t - 1) / B⌋₊, c h)
      = ∑ h ∈ Finset.Icc 1 N, c h * (if 1 + (h:ℝ) * B ≤ t then (1:ℝ) else 0)
    rw [Commons.Analysis.Floor.sum_Icc_floor_eq c hB hA hH]
    apply Finset.sum_congr rfl
    intro h hh
    have hiff : ((h:ℕ):ℝ) ≤ (t - 1) / B ↔ 1 + (h:ℝ) * B ≤ t := by
      rw [le_div_iff₀ hB]; constructor <;> intro h' <;> linarith
    by_cases hc : 1 + (h:ℝ) * B ≤ t
    · rw [if_pos (hiff.mpr hc), if_pos hc]
    · rw [if_neg (fun h' => hc (hiff.mp h')), if_neg hc]
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro h hh
    rw [intervalIntegral.integral_const_mul]
    rw [Commons.MeasureTheory.IntervalIntegral.integral_indicator_Ici (1:ℝ) (1 + (h:ℝ)*B) hv,
      one_mul]
  · intro h hh
    rw [intervalIntegrable_iff, Set.uIoc_of_le hv]
    refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top ?_ |c h| ?_
    · apply Measurable.aestronglyMeasurable
      apply Measurable.const_mul
      apply Measurable.ite
      · exact measurableSet_Ici
      · exact measurable_const
      · exact measurable_const
    · filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul]
      apply mul_le_of_le_one_right (abs_nonneg _)
      by_cases hc : 1 + (h:ℝ) * B ≤ t <;> simp [hc]

end Commons.Analysis.Floor
