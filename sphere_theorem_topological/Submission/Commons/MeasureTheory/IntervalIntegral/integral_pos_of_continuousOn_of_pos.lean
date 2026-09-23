import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.MeasureTheory.IntervalIntegral

theorem integral_pos_of_continuousOn_of_pos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hpos : ∀ x ∈ Set.Icc a b, 0 < f x) :
    0 < ∫ t in a..b, f t := by
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (hf.intervalIntegrable_of_Icc hab.le)
    (fun x hx => hpos x (Set.Ioo_subset_Icc_self hx)) hab

end Commons.MeasureTheory.IntervalIntegral