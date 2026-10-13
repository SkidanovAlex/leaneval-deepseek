import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Gradient.Basic
import Submission.Work.FTS.Top.Rescale.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Gradient
open scoped Gradient

namespace Work.FTS.Top

/-- **The gradient of a scalar multiple of a scalar-valued function**:
`∇ (fun y => a * g y) x = a • ∇ g x`.

This is unconditional — in particular it also holds at points where `g` is not differentiable:
when `a ≠ 0` the function `a * g` is then non-differentiable as well (divide by `a`), so both
sides are `0`; and when `a = 0` the left-hand side is the gradient of the zero function. -/
theorem gradient_const_mul (a : ℝ) (g : R3 → ℝ) (x : R3) :
    ∇ (fun y => a * g y) x = a • ∇ g x := by
  by_cases ha : a = 0
  · subst ha
    simp
  · by_cases hg : DifferentiableAt ℝ g x
    · -- differentiable case: compare Fréchet derivatives through `toDual`
      have hfd : fderiv ℝ (fun y => a * g y) x = a • fderiv ℝ g x := by
        have h1 : (fun y => a * g y) = (fun y => a • g y) := by
          funext y; rw [smul_eq_mul]
        rw [h1]
        rw [← Pi.smul_apply]
        exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := g) a) x
      rw [gradient, gradient, hfd]
      rw [map_smul]
    · -- non-differentiable case: `a * g` is non-differentiable too, both gradients vanish
      have hna : ¬ DifferentiableAt ℝ (fun y => a * g y) x := by
        intro h
        apply hg
        have hfun : (fun y => a⁻¹ * (a * g y)) = g := by
          funext y
          rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
        rw [← hfun]
        exact h.const_smul a⁻¹
      rw [gradient_eq_zero_of_not_differentiableAt hna,
        gradient_eq_zero_of_not_differentiableAt hg, smul_zero]

end Work.FTS.Top

namespace Work.FTS.Top.Rescale

/-
The gradient of the time-rescaled pressure.

`Work.FTS.Top.timeScaleP c p x t = c ^ 2 * p x (c * t)`, and the *space* variable is not rescaled,
so the gradient picks up exactly the factor `c ^ 2`.  The statement is unconditional: it holds for
`c = 0` too (`timeScaleP 0 p = 0` and `0 * ∇ = 0`).

Route: prove first the auxiliary fact `∇ (fun y => a * g y) x = a • ∇ g x` (unconditional in
Mathlib: in the differentiable case use `HasGradientAt.unique` with
`hasGradientAt_iff_hasFDerivAt`, `fderiv_const_smul_field` and `toDual_gradient`; in the
non-differentiable case `gradient_eq_zero_of_not_differentiableAt`, noting that `a • g` is
non-differentiable too when `a ≠ 0`, and that `a = 0` makes both sides `0`).
Then apply with `g = fun y => p y (c * t)` and `a = c ^ 2`, using `c ^ 2 * p y (c*t) = c^2 • p y (c*t)`.
Everything in namespace `Work.FTS.Top`.
-/
theorem spaceGrad_timeScaleP (c : ℝ) (p : Work.FTS.Top.R3 → ℝ → ℝ) (x : Work.FTS.Top.R3) (t : ℝ) :
    FiniteTimeSingularity.spaceGrad (Work.FTS.Top.timeScaleP c p) x t
      = (c * c) • FiniteTimeSingularity.spaceGrad p x (c * t) := by
  show ∇ (fun y => c ^ 2 * p y (c * t)) x = (c * c) • ∇ (fun y => p y (c * t)) x
  rw [pow_two]
  exact gradient_const_mul (c * c) (fun y => p y (c * t)) x

end Work.FTS.Top.Rescale
