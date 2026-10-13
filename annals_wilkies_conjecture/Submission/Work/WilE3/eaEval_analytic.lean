import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3

open Classical Topology

open WilkiesDesign.E

/-- `eaEval c Q` is real analytic.  Writing `z ↦ eaEval c Q z` as the composition of the
polynomial `Q` (via `MvPolynomial.aeval`) with the parametrisation
`z ↦ Sum.elim z (fun j => exp (c.ell j z))`, analyticity follows from
`AnalyticAt.aeval_mvPolynomial` applied to the analytic coordinate functions
`z ↦ z i` (a continuous linear projection) and `z ↦ exp (c.ell j z)` (exponential of the
affine form `c.ell j`). -/
theorem eaEval_analytic {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Q : WilkiesDesign.E.EAPoly k r)
    (x : Fin k → ℝ) : AnalyticAt ℝ (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Q z) x := by
  have hfun : (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Q z)
      = fun z => MvPolynomial.aeval (Sum.elim z (fun j => Real.exp (c.ell j z))) Q := by
    funext z
    simp [WilkiesDesign.E.eaEval, MvPolynomial.aeval_def]
  rw [hfun]
  refine AnalyticAt.aeval_mvPolynomial (𝕜 := ℝ) (A := ℝ) (B := ℝ)
    (f := fun z => Sum.elim z (fun j => Real.exp (c.ell j z))) ?_ Q
  intro i
  cases i with
  | inl i₀ =>
    have hcoord : (fun x : Fin k → ℝ => Sum.elim x (fun j => Real.exp (c.ell j x)) (Sum.inl i₀))
        = fun z => z i₀ := by
      funext z
      simp
    rw [hcoord]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i₀).analyticAt x
  | inr j₀ =>
    have hexp : (fun x : Fin k → ℝ => Sum.elim x (fun j => Real.exp (c.ell j x)) (Sum.inr j₀))
        = fun z => Real.exp (c.ell j₀ z) := by
      funext z
      simp
    rw [hexp]
    have hell : AnalyticAt ℝ (fun z : Fin k → ℝ => c.ell j₀ z) x := by
      have h1 : ∀ i ∈ (Finset.univ : Finset (Fin k)),
          AnalyticAt ℝ (fun z : Fin k → ℝ => c.a j₀ i * z i) x :=
        fun i _ => (analyticAt_const (v := c.a j₀ i)).mul
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).analyticAt x)
      have h2 : AnalyticAt ℝ ((∑ i : Fin k, fun z : Fin k → ℝ => c.a j₀ i * z i)) x :=
        Finset.analyticAt_sum (Finset.univ : Finset (Fin k)) h1
      have h2' : AnalyticAt ℝ (fun z : Fin k → ℝ => ∑ i, c.a j₀ i * z i) x := by
        simpa only [Finset.sum_fn] using h2
      have h3 : AnalyticAt ℝ (fun z : Fin k → ℝ => (∑ i, c.a j₀ i * z i) + c.b j₀) x :=
        h2'.add analyticAt_const
      simpa only [EAChain.ell] using h3
    exact hell.rexp'

end Work.WilE3
