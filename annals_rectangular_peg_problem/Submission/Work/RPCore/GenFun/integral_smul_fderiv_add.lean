import Mathlib

namespace Work.RPCore.GenFun

open MeasureTheory intervalIntegral

/-- Fundamental-theorem-of-calculus identity for the map `t ↦ t • b (t • y)`:

`∫ t in 0..1, (t • fderiv ℝ b (t • y) y + b (t • y)) = b y`.

The integrand is the derivative of `t ↦ t • b (t • y)` (product rule), and the integral
of a derivative over `[0,1]` is the difference of the endpoint values. -/
theorem integral_smul_fderiv_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (b : E → E) (hb : ContDiff ℝ 1 b) (y : E) :
    ∫ t in (0 : ℝ)..1, (t • fderiv ℝ b (t • y) y + b (t • y)) = b y := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => t • b (t • y))
      (t • fderiv ℝ b (t • y) y + b (t • y)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t) (1 : ℝ) t := hasDerivAt_id t
    have h2 : HasDerivAt (fun t : ℝ => t • y) y t := by
      simpa using (hasDerivAt_id t).smul_const y
    have h3 : HasDerivAt (fun t : ℝ => b (t • y)) (fderiv ℝ b (t • y) y) t := by
      have hb' : HasFDerivAt b (fderiv ℝ b (t • y)) (t • y) :=
        ((hb.differentiable (by norm_num)).differentiableAt).hasFDerivAt
      simpa [Function.comp_def] using hb'.comp_hasDerivAt t h2
    have h4 := h1.smul h3
    convert h4 using 1
    simp
  have hint : IntervalIntegrable (fun t : ℝ => t • fderiv ℝ b (t • y) y + b (t • y))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hfd : Continuous (fderiv ℝ b) := hb.continuous_fderiv (by norm_num)
    have hy : Continuous (fun t : ℝ => t • y) := continuous_id.smul continuous_const
    have hc1 : Continuous (fun t : ℝ => fderiv ℝ b (t • y) y) :=
      (hfd.comp hy).clm_apply continuous_const
    have hc2 : Continuous (fun t : ℝ => b (t • y)) := hb.continuous.comp hy
    exact (continuous_id.smul hc1).add hc2
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

end Work.RPCore.GenFun
