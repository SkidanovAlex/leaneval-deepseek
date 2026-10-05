import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

theorem contDiff_trigPoly (N : ℕ) (a : ℤ → ℂ) : ContDiff ℝ ∞ (trigPoly N a) := by
  unfold trigPoly
  refine ContDiff.sum (fun n _ => ?_)
  have hlin : ContDiff ℝ ∞ (fun t : ℝ => (n : ℂ) * (t : ℂ) * I) := by
    have h : ContDiff ℝ ∞ (fun t : ℝ => (n : ℂ) * (t : ℂ)) :=
      contDiff_const.mul Complex.ofRealCLM.contDiff
    simpa using h.mul (contDiff_const (c := I))
  have hexp : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp ((n : ℂ) * (t : ℂ) * I)) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).comp hlin
  simpa using (contDiff_const (c := a n)).mul hexp

end Work.RPB1a
