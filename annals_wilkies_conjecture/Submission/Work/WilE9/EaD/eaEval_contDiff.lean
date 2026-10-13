import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.EaD

/-- `eaEval c Q` is smooth. -/
theorem eaEval_contDiff {N r : ℕ} (c : WilkiesDesign.E.EAChain N r)
    (Q : WilkiesDesign.E.EAPoly N r) :
    ContDiff ℝ ⊤ (fun w : Fin N → ℝ => WilkiesDesign.E.eaEval c Q w) := by
  -- `eaEval c Q` is `MvPolynomial.aeval` of the assignment `x ↦ (x, exp (ℓ_j x))`, which is
  -- analytic: each coordinate is either a projection or `exp` of an affine function.
  apply AnalyticOnNhd.contDiff
  intro w _
  rw [show (fun x : Fin N → ℝ => WilkiesDesign.E.eaEval c Q x)
        = fun x => MvPolynomial.aeval (Sum.elim x (fun j => Real.exp (c.ell j x))) Q from by
      funext x; rw [MvPolynomial.aeval_eq_eval]; rfl]
  apply AnalyticAt.aeval_mvPolynomial
  intro i
  rcases i with a | j
  · exact ContinuousLinearMap.analyticAt (ContinuousLinearMap.proj a : (Fin N → ℝ) →L[ℝ] ℝ) w
  · have hell : AnalyticAt ℝ (fun x : Fin N → ℝ => c.ell j x) w := by
      have h1 : AnalyticAt ℝ (fun x : Fin N → ℝ => ∑ i, c.a j i * x i) w := by
        have h : (fun x : Fin N → ℝ => ∑ i, c.a j i * x i)
            = fun x => (∑ i, c.a j i •
                (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) x := by
          ext x; simp
        rw [h]
        exact ContinuousLinearMap.analyticAt _ w
      have h2 : (fun x : Fin N → ℝ => c.ell j x)
          = fun x => (∑ i, c.a j i * x i) + c.b j := by
        ext x; simp [WilkiesDesign.E.EAChain.ell]
      rw [h2]
      exact h1.add analyticAt_const
    rw [Real.exp_eq_exp_ℝ]
    exact AnalyticAt.comp (NormedSpace.exp_analytic (c.ell j w)) hell

end Work.WilE9.EaD
