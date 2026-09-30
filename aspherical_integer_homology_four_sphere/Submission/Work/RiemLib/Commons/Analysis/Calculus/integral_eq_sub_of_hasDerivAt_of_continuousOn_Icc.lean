import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.Calculus

theorem integral_eq_sub_of_hasDerivAt_of_continuousOn_Icc
    {F g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (h : ∀ x ∈ Set.Ioo a b, HasDerivAt F (g x) x) :
    ∫ x in a..b, g x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF h
    (hg.intervalIntegrable_of_Icc hab)

end Commons.Analysis.Calculus