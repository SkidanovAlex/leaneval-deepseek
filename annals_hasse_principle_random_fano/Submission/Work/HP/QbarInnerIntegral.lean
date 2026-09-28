import Mathlib

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Work.HP

lemma max_sq_le_one_iff (a y : ℝ) : max (a ^ 2) (y ^ 2) ≤ 1 ↔ |a| ≤ 1 ∧ |y| ≤ 1 := by
  rw [max_le_iff, sq_le_one_iff_abs_le_one, sq_le_one_iff_abs_le_one]

lemma sqrt_max_sq_eq (a y : ℝ) : Real.sqrt (max (a ^ 2) (y ^ 2)) = max |a| |y| := by
  have h : max (a ^ 2) (y ^ 2) = (max |a| |y|) ^ 2 := by
    rw [← sq_abs a, ← sq_abs y]
    rcases le_total |a| |y| with hle | hle
    · rw [max_eq_right hle, max_eq_right (by nlinarith [abs_nonneg a, abs_nonneg y])]
    · rw [max_eq_left hle, max_eq_left (by nlinarith [abs_nonneg a, abs_nonneg y])]
  rw [h, Real.sqrt_sq_eq_abs, abs_of_nonneg (le_trans (abs_nonneg a) (le_max_left |a| |y|))]

theorem QbarInnerIntegral (d : ℕ) (a : ℝ) :
    (∫ y : ℝ, (if max (a ^ 2) (y ^ 2) ≤ 1 then (Real.sqrt (max (a ^ 2) (y ^ 2))) ^ d else 0))
      = if |a| ≤ 1 then 2 * ((d : ℝ) * |a| ^ (d + 1) + 1) / ((d : ℝ) + 1) else 0 := by
  by_cases ha : |a| ≤ 1
  · rw [ite_eq_left ha]
    have hpt : (fun y : ℝ => (if max (a ^ 2) (y ^ 2) ≤ 1
          then (Real.sqrt (max (a ^ 2) (y ^ 2))) ^ d else 0))
        = fun y : ℝ => (if |y| ≤ 1 then (max |a| |y|) ^ d else 0) := by
      funext y
      by_cases hy : |y| ≤ 1
      · rw [ite_eq_left ((max_sq_le_one_iff a y).mpr ⟨ha, hy⟩), ite_eq_left hy, sqrt_max_sq_eq]
      · rw [ite_eq_right (fun h => hy ((max_sq_le_one_iff a y).mp h).2), ite_eq_right hy]
    rw [hpt]
    have hfun : (fun y : ℝ => (if |y| ≤ 1 then (max |a| |y|) ^ d else 0))
        = (Set.Icc (-1:ℝ) 1).indicator (fun y : ℝ => (max |a| |y|) ^ d) := by
      funext y
      by_cases hy : |y| ≤ 1
      · have hy' : y ∈ Set.Icc (-1:ℝ) 1 := by rw [Set.mem_Icc]; exact abs_le.mp hy
        rw [Set.indicator_of_mem hy', ite_eq_left hy]
      · have hy' : y ∉ Set.Icc (-1:ℝ) 1 := by
          rw [Set.mem_Icc]; intro h; exact hy (abs_le.mpr h)
        rw [Set.indicator_of_notMem hy', ite_eq_right hy]
    rw [hfun, integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show (-1:ℝ) ≤ 1 by norm_num)]
    have hcont : Continuous fun y : ℝ => (max |a| |y|) ^ d :=
      (continuous_const.max continuous_abs).pow d
    have hsplit : (∫ y in (-1:ℝ)..1, (max |a| |y|) ^ d)
        = (∫ y in (-1:ℝ)..0, (max |a| |y|) ^ d) + (∫ y in (0:ℝ)..1, (max |a| |y|) ^ d) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)).symm
    have hneg : (∫ y in (-1:ℝ)..0, (max |a| |y|) ^ d)
        = ∫ y in (0:ℝ)..1, (max |a| |y|) ^ d := by
      have h := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := 0)
        (f := fun t : ℝ => (max |a| |t|) ^ d)
      simpa using h
    rw [hsplit, hneg]
    have hA : (∫ y in (0:ℝ)..1, (max |a| |y|) ^ d)
        = ((d:ℝ) * |a| ^ (d + 1) + 1) / ((d:ℝ) + 1) := by
      have hcongr : (∫ y in (0:ℝ)..1, (max |a| |y|) ^ d)
          = ∫ y in (0:ℝ)..1, (max |a| y) ^ d := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy
        show (max |a| |y|) ^ d = (max |a| y) ^ d
        rw [abs_of_nonneg hy.1]
      rw [hcongr]
      have hcont2 : Continuous fun y : ℝ => (max |a| y) ^ d :=
        (continuous_const.max continuous_id).pow d
      have hsplit2 : (∫ y in (0:ℝ)..1, (max |a| y) ^ d)
          = (∫ y in (0:ℝ)..|a|, (max |a| y) ^ d) + (∫ y in |a|..1, (max |a| y) ^ d) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont2.intervalIntegrable 0 |a|) (hcont2.intervalIntegrable |a| 1)).symm
      rw [hsplit2]
      have h1 : (∫ y in (0:ℝ)..|a|, (max |a| y) ^ d) = |a| * |a| ^ d := by
        have e : (∫ y in (0:ℝ)..|a|, (max |a| y) ^ d) = ∫ y in (0:ℝ)..|a|, |a| ^ d := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [Set.uIcc_of_le (abs_nonneg a)] at hy
          show (max |a| y) ^ d = |a| ^ d
          rw [max_eq_left hy.2]
        rw [e, intervalIntegral.integral_const]
        simp
      have h2 : (∫ y in |a|..1, (max |a| y) ^ d) = (1 - |a| ^ (d + 1)) / ((d:ℝ) + 1) := by
        have e : (∫ y in |a|..1, (max |a| y) ^ d) = ∫ y in |a|..1, y ^ d := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [Set.uIcc_of_le ha] at hy
          show (max |a| y) ^ d = y ^ d
          rw [max_eq_right hy.1]
        rw [e, integral_pow, one_pow]
      rw [h1, h2, show |a| * |a| ^ d = |a| ^ (d + 1) by rw [mul_comm, ← pow_succ]]
      have hD1 : (d:ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hA, mul_div_assoc, two_mul]
  · rw [ite_eq_right ha]
    have h0 : (fun y : ℝ => (if max (a ^ 2) (y ^ 2) ≤ 1
          then (Real.sqrt (max (a ^ 2) (y ^ 2))) ^ d else 0)) = fun _ : ℝ => (0:ℝ) := by
      funext y
      rw [ite_eq_right (fun h => ha ((max_sq_le_one_iff a y).mp h).1)]
    rw [h0, integral_zero]

end Work.HP
