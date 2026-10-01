import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory intervalIntegral

namespace Commons.Analysis.Integral

/-- Elementary antiderivative:
`∫_{p}^{q} t²·log(c+t²) dt = [ (t³/3)log(c+t²) - (2/3)(t³/3 - c·t + c^(3/2)·arctan(t/√c)) ]_p^q`. -/
theorem integral_sq_mul_log_sq_add {c p q : ℝ} (hc : 0 < c) :
    (∫ t in p..q, t^2 * Real.log (c + t^2))
      = ((q^3/3)*Real.log (c+q^2) - (2/3)*(q^3/3 - c*q + c*Real.sqrt c*Real.arctan (q/Real.sqrt c)))
      - ((p^3/3)*Real.log (c+p^2) - (2/3)*(p^3/3 - c*p + c*Real.sqrt c*Real.arctan (p/Real.sqrt c))) := by
  have hsqrt_ne : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  let F : ℝ → ℝ := fun t =>
    (t^3/3)*Real.log (c+t^2) - (2/3)*(t^3/3 - c*t + c*Real.sqrt c*Real.arctan (t/Real.sqrt c))
  have hderiv : ∀ t ∈ Set.uIcc p q, HasDerivAt F (t^2 * Real.log (c+t^2)) t := by
    intro t ht
    show HasDerivAt (fun t => (t^3/3)*Real.log (c+t^2)
        - (2/3)*(t^3/3 - c*t + c*Real.sqrt c*Real.arctan (t/Real.sqrt c)))
        (t^2 * Real.log (c+t^2)) t
    have hnum : HasDerivAt (fun t : ℝ => t^3/3) (t^2) t := by
      have h := (hasDerivAt_pow 3 t).div_const (3 : ℝ)
      refine h.congr_deriv ?_
      norm_num
    have hct : HasDerivAt (fun t : ℝ => c * t) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    have hlog : HasDerivAt (fun t : ℝ => Real.log (c + t^2)) (2*t/(c+t^2)) t := by
      have hg : HasDerivAt (fun t : ℝ => c + t^2) (2*t) t := by
        have h := (hasDerivAt_pow 2 t).const_add c
        refine h.congr_deriv ?_
        norm_num
      exact hg.log (by positivity)
    have hA : HasDerivAt (fun t : ℝ => (t^3/3)*Real.log (c+t^2))
        (t^2 * Real.log (c+t^2) + (t^3/3)*(2*t/(c+t^2))) t := hnum.mul hlog
    have hinner : HasDerivAt (fun t : ℝ => t / Real.sqrt c) (1/Real.sqrt c) t :=
      (hasDerivAt_id t).div_const (Real.sqrt c)
    have harctan : HasDerivAt (fun t : ℝ => Real.arctan (t / Real.sqrt c))
        ((1 / (1 + (t / Real.sqrt c)^2)) * (1/Real.sqrt c)) t := hinner.arctan
    have hcst : HasDerivAt (fun t : ℝ => c * Real.sqrt c * Real.arctan (t / Real.sqrt c))
        (c * Real.sqrt c * ((1 / (1 + (t / Real.sqrt c)^2)) * (1/Real.sqrt c))) t :=
      harctan.const_mul (c * Real.sqrt c)
    have hB : HasDerivAt (fun t : ℝ => t^3/3 - c*t + c*Real.sqrt c*Real.arctan (t / Real.sqrt c))
        (t^2 - c + c * Real.sqrt c * ((1 / (1 + (t / Real.sqrt c)^2)) * (1/Real.sqrt c))) t :=
      (hnum.sub hct).add hcst
    have hmain := hA.sub (hB.const_mul (2/3))
    refine hmain.congr_deriv ?_
    have hYZ : (t^3/3)*(2*t/(c+t^2)) = (2/3)*(t^2 - c + c * Real.sqrt c * ((1 / (1 + (t / Real.sqrt c)^2)) * (1/Real.sqrt c))) := by
      have h1 : c + t^2 ≠ 0 := by positivity
      have h2 : 1 + (t/Real.sqrt c)^2 ≠ 0 := by positivity
      have hs2 : (Real.sqrt c)^2 = c := Real.sq_sqrt hc.le
      field_simp
      rw [hs2]
      ring
    rw [hYZ]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => t^2 * Real.log (c+t^2)) volume p q := by
    apply Continuous.intervalIntegrable
    have hlog : Continuous (fun t : ℝ => Real.log (c + t^2)) :=
      Continuous.log (by continuity) (fun t => by positivity)
    exact (continuous_id.pow 2).mul hlog
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
    (f' := fun t : ℝ => t^2 * Real.log (c+t^2)) hderiv hint
  simpa [F] using h

end Commons.Analysis.Integral