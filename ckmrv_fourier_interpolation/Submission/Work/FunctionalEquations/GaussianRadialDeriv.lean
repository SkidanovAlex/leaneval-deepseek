import Mathlib
import Submission.Work.FunctionalEquations.Basic

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- The derivative of `r ↦ exp (c * r ^ 2)` at a real point. -/
private lemma hasDerivAt_gaussianProfile (c : ℂ) (x : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.exp (c * (r : ℂ) ^ 2))
      (Complex.exp (c * (x : ℂ) ^ 2) * (c * (2 * (x : ℂ)))) x := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) ^ 2) ((2 : ℂ) * (x : ℂ)) x := by
    have h := (hasDerivAt_pow 2 x).ofReal_comp
    simpa using h
  have h2 : HasDerivAt (fun r : ℝ => c * (r : ℂ) ^ 2) (c * ((2 : ℂ) * (x : ℂ))) x :=
    h1.const_mul c
  simpa using h2.cexp

set_option linter.unusedVariables false in
theorem GaussianRadialDeriv {n : ℕ} [NeZero n] (τ : ℂ) (hτ : 0 < τ.im)
    (m : Set.Ici (1 : ℕ)) :
    radialDeriv 1 (Work.Core.gaussianFun n τ) (samplePoint (n := n) (m.1 : ℝ))
      = (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ)) * dirichletTerm m.1 τ := by
  have hnorm : ‖samplePoint (n := n) (m.1 : ℝ)‖ = Real.sqrt (2 * (m.1 : ℝ)) := by
    rw [samplePoint, Work.Sampling.realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [radialDeriv, iteratedDeriv_one, hnorm]
  -- The profile of the Gaussian is `r ↦ exp (π i τ r²)`.
  have hfun : (fun r : ℝ => Work.Core.gaussianFun n τ (realIncl (n := n) r))
      = fun r : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (r : ℂ) ^ 2) := by
    funext r
    rw [Work.Core.gaussianFun]
    congr 1
    rw [Work.Sampling.realIncl_norm, sq_abs]
    push_cast
    ring
  rw [hfun]
  rw [(hasDerivAt_gaussianProfile ((Real.pi : ℂ) * Complex.I * τ)
        (Real.sqrt (2 * (m.1 : ℝ)))).deriv]
  have hsq : ((Real.sqrt (2 * (m.1 : ℝ)) : ℂ)) ^ 2 = ((2 * (m.1 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  have hexp : Complex.exp ((Real.pi : ℂ) * Complex.I * τ *
        ((Real.sqrt (2 * (m.1 : ℝ)) : ℂ)) ^ 2) = dirichletTerm m.1 τ := by
    rw [hsq, dirichletTerm]
    congr 1
    push_cast
    ring
  rw [hexp, rate]
  ring

end Work.FunctionalEquations
