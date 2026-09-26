import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.E2_qExpansion_coeff
import Submission.Work.Modular.qExpansion_normalizedDerivOfComplex

/-!
# The normalized derivative of `E₂` vanishes at the cusp

The weight-two Eisenstein series `E₂` is holomorphic and `1`-periodic, so it factors as
`E₂ τ = g (𝕢 1 τ)` with `g = cuspFunction 1 E2` analytic at `0`.  Differentiating along the
`q`-parameter (`normalizedDeriv_eq_qParam_mul_deriv_cuspFunction`) gives

`D E₂ τ = 𝕢 1 τ · g' (𝕢 1 τ)`,

and since `𝕢 1 τ → 0` at the cusp (`qParam_tendsto_atImInfty`) while `g'` is continuous at `0`
(`AnalyticAt.deriv`), the limit is `0 · g' 0 = 0`.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped Manifold MatrixGroups ModularForm Topology

/-- The normalized derivative of `E₂` vanishes at the cusp `i∞`.  Route: with
`g = cuspFunction 1 E2` (analytic at `0` by `analyticAt_cuspFunction_zero`, using
`E2_periodic_one`, `E2_mdifferentiable` and `isBoundedAtImInfty_E2`), the chain rule applied to
`g (qParam 1 τ) = E2 τ` gives `D E₂ = fun τ => deriv g (qParam 1 τ) * qParam 1 τ`.  Then use
`UpperHalfPlane.qParam_tendsto_atImInfty` and continuity of `deriv g` at `0`
(`AnalyticAt.deriv`), so the limit is `deriv g 0 * 0 = 0`. -/
theorem D_E2_tendsto_atImInfty :
    Filter.Tendsto (Derivative.normalizedDerivOfComplex E2) UpperHalfPlane.atImInfty
      (𝓝 (0 : ℂ)) := by
  have hperi : Function.Periodic (E2 ∘ UpperHalfPlane.ofComplex) 1 := E2_periodic_one
  -- `g = cuspFunction 1 E2` is analytic at `0`, hence so is `deriv g`.
  have hana : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperi E2_mdifferentiable
      EisensteinSeries.isBoundedAtImInfty_E2
  have hcont : ContinuousAt (deriv (UpperHalfPlane.cuspFunction 1 E2)) 0 :=
    hana.deriv.continuousAt
  -- Both factors converge: `deriv g (𝕢 1 τ) → deriv g 0` and `𝕢 1 τ → 0`.
  have hq : Filter.Tendsto (fun τ : ℍ => Function.Periodic.qParam 1 (τ : ℂ))
      UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) :=
    UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  have hdg : Filter.Tendsto
      (fun τ : ℍ => deriv (UpperHalfPlane.cuspFunction 1 E2)
        (Function.Periodic.qParam 1 (τ : ℂ)))
      UpperHalfPlane.atImInfty
      (𝓝 (deriv (UpperHalfPlane.cuspFunction 1 E2) 0)) :=
    hcont.tendsto.comp hq
  have hlim := hdg.mul hq
  -- `D E₂` is pointwise this product, by the chain rule along the `q`-parameter.
  have hfun : (fun τ : ℍ => deriv (UpperHalfPlane.cuspFunction 1 E2)
        (Function.Periodic.qParam 1 (τ : ℂ)) * Function.Periodic.qParam 1 (τ : ℂ))
      = Derivative.normalizedDerivOfComplex E2 := by
    funext τ
    rw [normalizedDeriv_eq_qParam_mul_deriv_cuspFunction hperi E2_mdifferentiable τ, mul_comm]
  rw [hfun] at hlim
  simpa using hlim

end Work.Modular
