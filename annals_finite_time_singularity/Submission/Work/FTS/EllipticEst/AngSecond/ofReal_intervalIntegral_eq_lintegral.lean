import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

theorem ofReal_intervalIntegral_eq_lintegral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hnn : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in a..b, f x) = ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (f x) := by
  rw [intervalIntegral.integral_of_le hab]
  rw [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · exact (hf.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  · change ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioc a b), 0 ≤ f x
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun x hx => hnn x (Set.Ioc_subset_Icc_self hx)

end Work.FTS.EllipticEst.AngSecond
