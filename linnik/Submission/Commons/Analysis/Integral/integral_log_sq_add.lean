import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Integral

/-- Elementary antiderivative: `∫_{p}^{q} log(c+t²) dt = [t·log(c+t²) - 2t + 2√c·arctan(t/√c)]_p^q`. -/
theorem integral_log_sq_add {c p q : ℝ} (hc : 0 < c) :
    (∫ t in p..q, Real.log (c + t^2))
      = (q*Real.log (c+q^2) - 2*q + 2*Real.sqrt c*Real.arctan (q/Real.sqrt c))
      - (p*Real.log (c+p^2) - 2*p + 2*Real.sqrt c*Real.arctan (p/Real.sqrt c)) := by
  -- `log (c + t²)` is continuous, hence interval integrable on `[p, q]`
  have hcont : Continuous (fun x : ℝ => Real.log (c + x^2)) :=
    (by fun_prop : Continuous (fun x : ℝ => c + x^2)).log (fun x => by positivity)
  -- the antiderivative `F(t) = t·log(c+t²) - 2t + 2√c·arctan(t/√c)` has derivative `log(c+t²)`
  have hderiv : ∀ x ∈ Set.uIcc p q,
      HasDerivAt
        (fun t : ℝ => t * Real.log (c + t^2) - 2*t + 2*Real.sqrt c * Real.arctan (t/Real.sqrt c))
        (Real.log (c + x^2)) x := by
    intro x _
    have hct : c + x^2 ≠ 0 := by positivity
    have hs2 : (Real.sqrt c)^2 = c := Real.sq_sqrt hc.le
    -- derivative of `t ↦ t·log(c+t²)`
    have h1 : HasDerivAt (fun t : ℝ => t * Real.log (c + t^2))
        (1 * Real.log (c + x^2) + x * ((c + x^2)⁻¹ * (2*x))) x := by
      have hinner : HasDerivAt (fun t : ℝ => c + t^2) (2*x) x := by
        have hh : HasDerivAt (fun t : ℝ => (c:ℝ) + t^2) ((0:ℝ) + 2 * x^(2-1)) x :=
          (hasDerivAt_const x c).add (hasDerivAt_pow 2 x)
        simpa using hh
      have hcomp := (Real.hasDerivAt_log hct).comp x hinner
      exact (hasDerivAt_id x).mul hcomp
    -- derivative of `t ↦ 2t`
    have h2 : HasDerivAt (fun t : ℝ => 2*t) 2 x := by
      have hh : HasDerivAt (fun t : ℝ => (2:ℝ)*t) ((2:ℝ)*1) x := (hasDerivAt_id x).const_mul (2:ℝ)
      simpa using hh
    -- derivative of `t ↦ 2√c·arctan(t/√c)`
    have h3 : HasDerivAt (fun t : ℝ => 2*Real.sqrt c * Real.arctan (t/Real.sqrt c))
        (2*Real.sqrt c * (1/(1+(x/Real.sqrt c)^2) * (1/Real.sqrt c))) x := by
      have hin : HasDerivAt (fun t : ℝ => t / Real.sqrt c) (1 / Real.sqrt c) x :=
        (hasDerivAt_id x).div_const (Real.sqrt c)
      have hcomp := (Real.hasDerivAt_arctan (x/Real.sqrt c)).comp x hin
      exact hcomp.const_mul (2*Real.sqrt c)
    have h := (h1.sub h2).add h3
    -- the total derivative collapses to `log(c + x²)`
    have hval : (1 * Real.log (c + x ^ 2) + x * ((c + x ^ 2)⁻¹ * (2 * x)) - 2
        + 2 * Real.sqrt c * (1 / (1 + (x / Real.sqrt c) ^ 2) * (1 / Real.sqrt c)))
        = Real.log (c + x^2) := by
      field_simp
      nlinarith [hs2]
    rw [hval] at h
    exact h
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable p q)

end Commons.Analysis.Integral