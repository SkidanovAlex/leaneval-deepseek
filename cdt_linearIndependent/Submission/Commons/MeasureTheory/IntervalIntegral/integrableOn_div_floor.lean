import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Commons.MeasureTheory.IntervalIntegral

theorem integrableOn_div_floor (c w : ℝ) {B : ℝ} (hB : 0 < B) (v : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => max (t / ((⌊(t + c) / B⌋₊ : ℕ) : ℝ) - w) 0) (Set.Icc 1 v) := by
  set C : ℝ := max |w| (max (v - w) 0) with hC
  refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top ?_ C ?_
  · exact (by fun_prop : Measurable fun t : ℝ =>
        max (t / ((⌊(t + c) / B⌋₊ : ℕ) : ℝ) - w) 0).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    obtain ⟨hx1, hxv⟩ := hx
    have hxpos : (0:ℝ) ≤ x := le_trans zero_le_one hx1
    have hvpos : (0:ℝ) ≤ v := le_trans hxpos hxv
    have hCnn : 0 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    have key : max (x / ((⌊(x + c) / B⌋₊ : ℕ) : ℝ) - w) 0 ≤ C := by
      rcases Nat.eq_zero_or_pos ⌊(x + c) / B⌋₊ with hn | hn
      · rw [hn]
        simp only [Nat.cast_zero, div_zero, zero_sub]
        exact max_le (le_trans (neg_le_abs w) (le_max_left _ _))
          (le_trans (le_max_right _ _) (le_max_right _ _))
      · have hn1 : 1 ≤ ⌊(x + c) / B⌋₊ := Nat.succ_le_of_lt hn
        have hnv : (1:ℝ) ≤ ((⌊(x + c) / B⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn1
        have hnpos : (0:ℝ) < ((⌊(x + c) / B⌋₊ : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hnv
        have hdiv : x / ((⌊(x + c) / B⌋₊ : ℕ) : ℝ) ≤ v := by
          rw [div_le_iff₀ hnpos]
          calc x ≤ v := hxv
            _ = v * 1 := (mul_one v).symm
            _ ≤ v * ((⌊(x + c) / B⌋₊ : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hnv hvpos
        exact max_le (le_trans (sub_le_sub_right hdiv w)
          (le_trans (le_max_left _ _) (le_max_right _ _))) hCnn
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact key

end Commons.MeasureTheory.IntervalIntegral