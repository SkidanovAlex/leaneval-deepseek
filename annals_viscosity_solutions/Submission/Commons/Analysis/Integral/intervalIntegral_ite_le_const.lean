import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace Commons.Analysis.Integral

theorem intervalIntegral_ite_le_const {a b c K : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ t in a..b, (if t ≤ c then 0 else K) = (b - c) * K := by
  have hmeas : Measurable (fun t : ℝ => if t ≤ c then 0 else K) :=
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hint : ∀ p q : ℝ, IntervalIntegrable (fun t : ℝ => if t ≤ c then 0 else K) volume p q := by
    intro p q
    refine IntervalIntegrable.mono_fun' (g := fun _ : ℝ => |K|) intervalIntegrable_const
      hmeas.aestronglyMeasurable ?_
    filter_upwards with x
    by_cases hx : x ≤ c
    · simp [hx]
    · simp [hx]
  have h1 : ∫ t in a..c, (if t ≤ c then 0 else K) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0:ℝ)) (fun x hx => by
          rw [Set.uIcc_of_le hac] at hx
          simp [if_pos hx.2]),
      intervalIntegral.integral_zero]
  have h2 : ∫ t in c..b, (if t ≤ c then 0 else K) = (b - c) * K := by
    rw [intervalIntegral.integral_congr_Ioo_of_le (f := fun t => if t ≤ c then 0 else K)
          (g := fun _ : ℝ => K) hcb (fun x hx => by simp [if_neg (not_le.mpr hx.1)]),
      intervalIntegral.integral_const, smul_eq_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint a c) (hint c b), h1, h2, zero_add]

end Commons.Analysis.Integral