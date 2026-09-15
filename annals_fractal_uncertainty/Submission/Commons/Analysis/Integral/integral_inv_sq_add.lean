import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Integral

/-- Elementary antiderivative: `∫_{p}^{q} k/(k²+t²) dt = arctan(q/k) - arctan(p/k)` for `k > 0`. -/
theorem integral_inv_sq_add {k p q : ℝ} (hk : 0 < k) :
    (∫ t in p..q, k/(k^2 + t^2)) = Real.arctan (q/k) - Real.arctan (p/k) := by
  have hderiv : ∀ x ∈ Set.uIcc p q,
      HasDerivAt (fun t : ℝ => Real.arctan (t/k)) (k/(k^2 + x^2)) x := by
    intro x _
    have hin : HasDerivAt (fun t : ℝ => t/k) (1/k) x :=
      (hasDerivAt_id x).div_const k
    have h := (Real.hasDerivAt_arctan (x/k)).comp x hin
    refine h.congr_deriv ?_
    have h1 : k^2 + x^2 ≠ 0 := by positivity
    have hk' : k ≠ 0 := ne_of_gt hk
    field_simp
  have hcont : Continuous (fun t : ℝ => k/(k^2 + t^2)) :=
    Continuous.div continuous_const (continuous_const.add (continuous_id.pow 2))
      (fun t => by positivity)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => Real.arctan (t/k))
    (f' := fun t : ℝ => k/(k^2 + t^2)) hderiv (hcont.intervalIntegrable p q)
  simpa using h

end Commons.Analysis.Integral
