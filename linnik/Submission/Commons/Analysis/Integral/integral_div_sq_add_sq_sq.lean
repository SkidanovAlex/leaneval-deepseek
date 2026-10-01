import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Integral

open MeasureTheory

/-- The function `t ↦ t/(2c(c²+t²)) + arctan(t/c)/(2c²)` is an antiderivative of
`t ↦ c/(c²+t²)²` for `c > 0`. -/
theorem hasDerivAt_div_sq_add_sq_sq {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (fun t : ℝ => t/(2*c*(c^2+t^2)) + Real.arctan (t/c)/(2*c^2))
      (c/(c^2+x^2)^2) x := by
  have hinner : HasDerivAt (fun s : ℝ => c^2 + s^2) (2*x) x := by
    have h : HasDerivAt (fun s : ℝ => s^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
    simpa using h.const_add (c^2)
  have hg : HasDerivAt (fun s : ℝ => 2*c*(c^2+s^2)) (2*c*(2*x)) x := hinner.const_mul (2*c)
  have hgne : 2*c*(c^2+x^2) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => s/(2*c*(c^2+s^2))) ((c^2-x^2)/(2*c*(c^2+x^2)^2)) x := by
    refine ((hasDerivAt_id x).div hg hgne).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have h2 : HasDerivAt (fun s : ℝ => Real.arctan (s/c)/(2*c^2)) (1/(2*c*(c^2+x^2))) x := by
    have hin : HasDerivAt (fun s : ℝ => s/c) (1/c) x := (hasDerivAt_id x).div_const c
    refine ((Real.hasDerivAt_arctan (x/c)).comp x hin |>.div_const (2*c^2)).congr_deriv ?_
    field_simp
  refine (h1.add h2).congr_deriv ?_
  field_simp
  ring

theorem integral_div_sq_add_sq_sq {c a b : ℝ} (hc : 0 < c) :
    (∫ t in a..b, c/(c^2+t^2)^2)
      = (b/(2*c*(c^2+b^2)) - a/(2*c*(c^2+a^2)))
        + (Real.arctan (b/c) - Real.arctan (a/c))/(2*c^2) := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => t/(2*c*(c^2+t^2)) + Real.arctan (t/c)/(2*c^2))
        (c/(c^2+x^2)^2) x := fun x _ => hasDerivAt_div_sq_add_sq_sq hc x
  have hcont : Continuous (fun t : ℝ => c/(c^2+t^2)^2) := by
    apply Continuous.div continuous_const
    · fun_prop
    · intro t
      positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t/(2*c*(c^2+t^2)) + Real.arctan (t/c)/(2*c^2))
    (f' := fun t : ℝ => c/(c^2+t^2)^2) hderiv (hcont.intervalIntegrable a b)
  rw [h]
  ring_nf

end Commons.Analysis.Integral
