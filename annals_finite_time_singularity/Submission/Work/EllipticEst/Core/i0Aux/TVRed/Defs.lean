/-
Copyright: work module for the Elgindi finite-time singularity project.

# Reduction of the open-class angular interpolation to the trace-vanishing case

`thetaInterpCoreOfTraceVanishing` derives, from the *trace-vanishing* weighted slice
interpolation `TV` (a hypothesis), the same inequality for the class of functions whose only
endpoint hypothesis is the *value* condition `f 0 = f (π/2) = 0` — the traces `lim_{0⁺} f`,
`lim_{(π/2)⁻} f` being allowed to be non-zero.

The reduction is by subtracting from `f` a *surrogate* `ℓ = surrFun ψ F₀ F₁ L` which
reproduces the two traces of `f` (`F₀ = lim_{0⁺} f`, `F₁ = lim_{(π/2)⁻} f`) and whose
weighted energy is controlled at a scale `L` tied to the data
(`L⁴ = P / (16 (P+E))`, `P = ∫ f²σ`, `E = ∫ (f'')²σ`).  Then `g = f - ℓ` has vanishing
traces, so `TV` applies to `g`, and the defect `A(f) - A(g)` is estimated by one integration
by parts against the surrogate.

## Contents of this file

* `qTh` — the logarithmic derivative factor of the weight: `(thEta)' = -qTh * thEta`;
* `surrFun ψ F₀ F₁ L` — the two-sided trace-matching surrogate;
* `IsBump ψ C` — the structure satisfied by the bump `ψ` used in the surrogate.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The angular factor `q(θ) = 2 η cot(2θ)` of the logarithmic derivative of the weight
`thEta θ = sin(2θ)^{-η}`, so that `thEta' = -qTh * thEta` on `(0, π/2)`. -/
noncomputable def qTh (θ : ℝ) : ℝ := 2 * Work.Spaces.eta * Real.cot (2 * θ)

/-- The two-sided trace-matching surrogate attached to a bump `ψ`:
`surrFun ψ F₀ F₁ L θ = F₀ * ψ (θ / L) + F₁ * ψ ((π/2 - θ) / L)`.
For a bump with `ψ = 1` on `(-∞, 1/4]` and `ψ = 0` on `[1/2, ∞)` its one-sided limits at `0⁺`
and `(π/2)⁻` are `F₀` and `F₁`, and its first two derivatives are supported in the two shells
`(L/4, L/2)` and `(π/2 - L/2, π/2 - L/4)`. -/
noncomputable def surrFun (ψ : ℝ → ℝ) (F₀ F₁ L θ : ℝ) : ℝ :=
  F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L)

/-- The structure of the bump `ψ` used to build the surrogate: it is `C²` (with the two
chain-rule data `HasDerivAt` fields), equals `1` on `(-∞, 1/4]`, equals `0` on `[1/2, ∞)`,
takes values in `[0,1]`, and its first two derivatives are bounded by `C` and vanish off the
shell `(1/4, 1/2)`. -/
structure IsBump (ψ : ℝ → ℝ) (C : ℝ) : Prop where
  /-- the bound is positive. -/
  C_pos : 0 < C
  /-- `ψ` is of class `C²`. -/
  contDiff : ContDiff ℝ 2 ψ
  /-- the first derivative exists at every point. -/
  hasDerivAt : ∀ x : ℝ, HasDerivAt ψ (deriv ψ x) x
  /-- the derivative of `ψ` is differentiable at every point. -/
  hasDerivAt_deriv : ∀ x : ℝ, HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x
  /-- `ψ = 1` on `(-∞, 1/4]`. -/
  eq_one : ∀ x : ℝ, x ≤ 1 / 4 → ψ x = 1
  /-- `ψ = 0` on `[1/2, ∞)`. -/
  eq_zero : ∀ x : ℝ, 1 / 2 ≤ x → ψ x = 0
  /-- `ψ ≥ 0`. -/
  nonneg : ∀ x : ℝ, 0 ≤ ψ x
  /-- `ψ ≤ 1`. -/
  le_one : ∀ x : ℝ, ψ x ≤ 1
  /-- the first derivative is bounded by `C`. -/
  deriv_bound : ∀ x : ℝ, |deriv ψ x| ≤ C
  /-- the second derivative is bounded by `C`. -/
  deriv2_bound : ∀ x : ℝ, |deriv (deriv ψ) x| ≤ C
  /-- the first derivative vanishes on `(-∞, 1/4)`. -/
  deriv_eq_zero_left : ∀ x : ℝ, x < 1 / 4 → deriv ψ x = 0
  /-- the first derivative vanishes on `(1/2, ∞)`. -/
  deriv_eq_zero_right : ∀ x : ℝ, 1 / 2 < x → deriv ψ x = 0
  /-- the second derivative vanishes on `(-∞, 1/4)`. -/
  deriv2_eq_zero_left : ∀ x : ℝ, x < 1 / 4 → deriv (deriv ψ) x = 0
  /-- the second derivative vanishes on `(1/2, ∞)`. -/
  deriv2_eq_zero_right : ∀ x : ℝ, 1 / 2 < x → deriv (deriv ψ) x = 0

end Work.EllipticEst.Core.i0Aux
