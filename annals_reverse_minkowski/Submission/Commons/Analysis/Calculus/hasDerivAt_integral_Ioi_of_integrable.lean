import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Commons.Analysis.Calculus

open MeasureTheory Set Filter
open scoped Real Topology

/-- Newton--Leibniz for the upper limit of an integral over a half-line: for a continuous
integrable `f : ℝ → ℝ`, the map `x ↦ ∫_{s > x} f s` has derivative `-f x`. -/
theorem hasDerivAt_integral_Ioi_of_integrable (f : ℝ → ℝ) (hc : Continuous f)
    (hint : Integrable f) (t : ℝ) :
    HasDerivAt (fun x => ∫ s in Set.Ioi x, f s) (-(f t)) t := by
  -- Fix a point `R > t`.  Then for every `x`, `∫_{s>x} f = ∫_{x}^{R} f + ∫_{s>R} f`,
  -- the last term being a constant.  The moving lower limit `x ↦ ∫_{x}^{R} f` has
  -- derivative `-f t`, and adding the constant does not change the derivative.
  set R : ℝ := t + 1 with hR
  have hfun : (fun x => ∫ s in Set.Ioi x, f s)
      = fun x => (∫ s in x..R, f s) + (∫ s in Set.Ioi R, f s) := by
    funext x
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (μ := volume)
      (hint.integrableOn (s := Set.Ioi x)) (hint.integrableOn (s := Set.Ioi R))
    linarith [h]
  rw [hfun]
  have hderiv : HasDerivAt (fun x : ℝ => ∫ s in x..R, f s) (-(f t)) t :=
    intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable t R)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa using hderiv.add_const (∫ s in Set.Ioi R, f s)

end Commons.Analysis.Calculus
