import Mathlib
import Submission.Work.ZeroDensity.HB7PoleKIntegral

namespace Work.ZeroDensity

open MeasureTheory Complex

/-- The Gram (pole) kernel `(e^{-y/X} - e^{-y/U'})·y^{w-1}` is absolutely integrable on `(0,∞)`
whenever `X > 0`, `U' > 0` and `Re w > 0`: it is the difference of the two integrable kernels
`e^{-y/X}·y^{w-1}` and `e^{-y/U'}·y^{w-1}`. -/
lemma HB7PoleGramIntegrable {X U' : ℝ} (hX : 0 < X) (hU' : 0 < U') {w : ℂ} (hw : 0 < w.re) :
    MeasureTheory.IntegrableOn (fun y : ℝ =>
      ((Real.exp (-(y / X)) - Real.exp (-(y / U')) : ℝ) : ℂ) * (y : ℂ) ^ (w - 1))
      (Set.Ioi (0 : ℝ)) := by
  have h1 := hb7PoleK_integrableOn_exp_neg_div_mul_cpow (r := X) hX hw
  have h2 := hb7PoleK_integrableOn_exp_neg_div_mul_cpow (r := U') hU' hw
  have hfun : (fun y : ℝ =>
        ((Real.exp (-(y / X)) - Real.exp (-(y / U')) : ℝ) : ℂ) * (y : ℂ) ^ (w - 1))
      = (fun y : ℝ => ((Real.exp (-(y / X)) : ℝ) : ℂ) * (y : ℂ) ^ (w - 1))
        - (fun y : ℝ => ((Real.exp (-(y / U')) : ℝ) : ℂ) * (y : ℂ) ^ (w - 1)) := by
    funext y
    simp only [Pi.sub_apply]
    rw [Complex.ofReal_sub]
    ring
  rw [hfun]
  exact h1.sub h2

end Work.ZeroDensity
