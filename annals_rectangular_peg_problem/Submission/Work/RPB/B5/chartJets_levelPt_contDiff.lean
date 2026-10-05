import Mathlib
import Submission.Work.RPV.Defs

namespace Work.RPB.B5

/-- `levelPt` is smooth in its three arguments `(u, σ, a)`, hence `C⁸` on the chart
`ℂ × (ℝ × ℝ) ∋ p ↦ levelPt p.1 p.2.1 p.2.2`.

The proof rewrites `levelPt` in terms of continuous linear maps (`Complex.reCLM`,
`Complex.imCLM`, `Complex.ofRealCLM`) and the entire function `Complex.exp`, for
which the `ContDiff` API is available, and then discharges the smoothness goal with
`fun_prop`.  The real-coordinate rewriting of `‖u‖ ^ 2` uses `Complex.sq_norm` and
`Complex.normSq_apply`. -/
theorem chartJets_levelPt_contDiff :
    ContDiff ℝ 8 (fun p : ℂ × (ℝ × ℝ) => Work.RPV.levelPt p.1 p.2.1 p.2.2) := by
  have h : (fun p : ℂ × (ℝ × ℝ) => Work.RPV.levelPt p.1 p.2.1 p.2.2)
      = fun p : ℂ × (ℝ × ℝ) =>
         (((Complex.imCLM (Complex.exp (-(Complex.ofRealCLM p.2.2) * Complex.I) * p.1), p.2.2)),
          ((Complex.reCLM (Complex.exp (-(Complex.ofRealCLM p.2.2) * Complex.I) * p.1)),
           (Complex.reCLM p.1 * Complex.reCLM p.1 + Complex.imCLM p.1 * Complex.imCLM p.1) / 2
             - p.2.1 - 1)) := by
    funext p
    simp only [Work.RPV.levelPt]
    ext <;> simp only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.sq_norm, Complex.normSq_apply]
  rw [h]
  fun_prop

end Work.RPB.B5
