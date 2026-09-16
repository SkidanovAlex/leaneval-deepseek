import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Commons.Analysis.Integral

open MeasureTheory Set
open scoped ENNReal

theorem abs_integral_Ioi_le_thin {G : ℝ → ℝ} {β η B : ℝ} (hη : 0 ≤ η)
    (hthin : ∀ u : ℝ, 0 ≤ u → G u ≠ 0 → β - 6 * η < u ∧ u < β)
    (hBbd : ∀ u : ℝ, |G u| ≤ B) :
    |∫ x in Set.Ioi (0:ℝ), G x| ≤ 6 * η * B := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hBbd 0)
  set s : Set ℝ := Set.Ioo (β - 6 * η) β with hs
  have hG0 : ∀ x : ℝ, 0 ≤ x → x ∉ s → G x = 0 := by
    intro x hx hxs
    by_contra hne
    exact hxs (hthin x hx hne)
  have h1 : ∫ x in Set.Ioi (0:ℝ), G x = ∫ x in Set.Ioi (0:ℝ) ∩ s, G x := by
    rw [← setIntegral_indicator (s := Set.Ioi (0:ℝ)) (t := s) measurableSet_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    by_cases hxs : x ∈ s
    · rw [indicator_of_mem hxs]
    · rw [indicator_of_notMem hxs, hG0 x hx.le hxs]
  have hfin : volume s < ∞ := by
    rw [hs, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hmeasfin : volume (Set.Ioi (0:ℝ) ∩ s) < ∞ :=
    lt_of_le_of_lt (measure_mono inter_subset_right) hfin
  have hbdd : ∀ x ∈ Set.Ioi (0:ℝ) ∩ s, ‖G x‖ ≤ B := by
    intro x _
    rw [Real.norm_eq_abs]
    exact hBbd x
  have hbound : ‖∫ x in Set.Ioi (0:ℝ) ∩ s, G x‖ ≤ B * volume.real (Set.Ioi (0:ℝ) ∩ s) :=
    norm_setIntegral_le_of_norm_le_const hmeasfin hbdd
  have hmono : volume.real (Set.Ioi (0:ℝ) ∩ s) ≤ volume.real s :=
    measureReal_mono inter_subset_right
  have hvol : volume.real s = 6 * η := by
    have h0 : 0 ≤ β - (β - 6 * η) := by linarith
    rw [hs, Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal h0]
    ring
  calc
    |∫ x in Set.Ioi (0:ℝ), G x| = |∫ x in Set.Ioi (0:ℝ) ∩ s, G x| := by rw [h1]
    _ = ‖∫ x in Set.Ioi (0:ℝ) ∩ s, G x‖ := by rw [Real.norm_eq_abs]
    _ ≤ B * volume.real (Set.Ioi (0:ℝ) ∩ s) := hbound
    _ ≤ B * volume.real s := mul_le_mul_of_nonneg_left hmono hB
    _ = B * (6 * η) := by rw [hvol]
    _ = 6 * η * B := by ring

end Commons.Analysis.Integral