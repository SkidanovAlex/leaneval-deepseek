import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.E2_qExpansion_coeff

/-!
# The weight-two Eisenstein series at the cusp

`E₂(τ) = 1 - 24 ∑_{n ≥ 1} σ₁(n) qⁿ` with `q = exp(2πiτ)`.  Since `q → 0` as
`im τ → ∞`, the series tends to its constant term `1` at the cusp `i∞`.

The argument is the standard `q`-expansion argument: a function `f` on `ℍ` that is
periodic of period `1`, holomorphic and bounded at `i∞` is written as `F(q)` for a
function `F = cuspFunction 1 f` analytic at `0`, and its value at the cusp is the
constant term `F 0 = valueAtInfty f` of the `q`-expansion.  Here we feed `f = E₂` into
`cuspFunction_apply_zero` / `qExpansion_coeff_zero`, using the periodicity of `E₂`
(`E2_periodic_one`), its holomorphy (`E2_mdifferentiable`) and boundedness at the cusp
(`EisensteinSeries.isBoundedAtImInfty_E2`), and identify the constant term with `1` via
the explicit `q`-expansion coefficients (`E2_qExpansion_coeff`).
-/

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped Manifold MatrixGroups ModularForm Topology

/-- The weight-two Eisenstein series `E₂` tends to its constant term `1` at the cusp `i∞`. -/
theorem E2_tendsto_atImInfty :
    Filter.Tendsto E2 UpperHalfPlane.atImInfty (𝓝 (1 : ℂ)) := by
  -- `E₂` is periodic of period one, holomorphic, and bounded at the cusp.
  have hperi : Function.Periodic (E2 ∘ UpperHalfPlane.ofComplex) 1 := E2_periodic_one
  have hanalytic : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperi E2_mdifferentiable
      EisensteinSeries.isBoundedAtImInfty_E2
  -- Hence `E₂ = F ∘ q` with `F` analytic at `0`, so it tends to `F 0` along `i∞`.
  have hcomp : Filter.Tendsto
      (fun τ : ℍ ↦ UpperHalfPlane.cuspFunction 1 E2 (Function.Periodic.qParam 1 (τ : ℂ)))
      UpperHalfPlane.atImInfty (𝓝 (UpperHalfPlane.cuspFunction 1 E2 0)) :=
    hanalytic.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)
  have hfeq : (fun τ : ℍ ↦ UpperHalfPlane.cuspFunction 1 E2
      (Function.Periodic.qParam 1 (τ : ℂ))) = E2 := by
    funext τ
    exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero hperi
  rw [hfeq] at hcomp
  -- The value at the cusp is the constant term of the `q`-expansion, which is `1`.
  have hval : UpperHalfPlane.cuspFunction 1 E2 0 = 1 := by
    rw [UpperHalfPlane.cuspFunction_apply_zero one_pos hanalytic hperi,
      ← UpperHalfPlane.qExpansion_coeff_zero one_pos hanalytic hperi]
    simpa using E2_qExpansion_coeff 0
  rwa [hval] at hcomp

end Work.Modular
