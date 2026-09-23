import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Calculus

theorem integral_eq_sub_of_hasDerivAt_of_continuousOn_Icc
    {F g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (h : ∀ x ∈ Set.Ioo a b, HasDerivAt F (g x) x) :
    ∫ x in a..b, g x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF h
    (hg.intervalIntegrable_of_Icc hab)

end Commons.Analysis.Calculus