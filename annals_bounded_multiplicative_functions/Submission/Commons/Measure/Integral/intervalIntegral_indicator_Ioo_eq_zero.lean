import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Measure.Integral

theorem intervalIntegral_indicator_Ioo_eq_zero {f : ℝ → ℂ} {a b p q : ℝ}
    (hdisj : ∀ u ∈ Set.uIcc a b, u ∉ Set.Ioo p q) :
    (∫ u in a..b,
        Set.indicator (Set.Ioo p q) (fun _ : ℝ => (1 : ℂ)) u * f u
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℂ))
        (fun u hu => by
          rw [Set.indicator_of_notMem (hdisj u hu)]
          simp)]
  simp

end Commons.Measure.Integral