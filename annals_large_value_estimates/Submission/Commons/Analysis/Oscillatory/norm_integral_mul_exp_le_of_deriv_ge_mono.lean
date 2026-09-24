import Mathlib
import Submission.Commons.Analysis.Oscillatory.poly_first_derivative_test
import Submission.Commons.Analysis.Oscillatory.norm_integral_mul_exp_le_of_hasDerivAt_deriv_ge_mono

namespace Commons.Analysis.Oscillatory

open MeasureTheory Set
open scoped Real Interval

/-- Oscillatory integral bound for a `C¹` weight `g`: if `φ` is `C²`, its
derivative is monotone on `[a,b]` and bounded below in absolute value by
`lam > 0`, then `∫ g(t) e^{iφ(t)}` is `O(|g a| + ∫|g'|)/lam`. -/
theorem norm_integral_mul_exp_le_of_deriv_ge_mono {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hmono : MonotoneOn (deriv φ) (Set.Icc a b) ∨ AntitoneOn (deriv φ) (Set.Icc a b))
    (hbound : ∀ t ∈ Set.Icc a b, lam ≤ |deriv φ t|)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    ‖(∫ t in a..b, (g t : ℂ) * Complex.exp (Complex.I * (φ t : ℂ)))‖
      ≤ 4 * (|g a| + ∫ t in a..b, |deriv g t|) / lam := by
  have hgc : ContinuousOn g (Set.Icc a b) := hg.continuous.continuousOn
  have hgd : ContinuousOn (deriv g) (Set.Icc a b) :=
    (hg.continuous_deriv (by norm_num)).continuousOn
  have hgderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt g (deriv g t) t := by
    intro t _
    exact (hg.differentiable (by norm_num)).differentiableAt.hasDerivAt
  exact norm_integral_mul_exp_le_of_hasDerivAt_deriv_ge_mono hab hlam hφ hmono hbound
    hgc hgd hgderiv

end Commons.Analysis.Oscillatory
