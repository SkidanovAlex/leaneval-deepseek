/-
Copyright: work module for the Elgindi finite-time singularity project.

# Subtracting under the elliptic operator `L` of (PolarBSL)

`Work.Elliptic.bslOp α Ψ = -α²z²∂_zzΨ - α(5+α)z∂_zΨ + L₀Ψ` with
`L₀Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` (see `Submission/Work/Elliptic/Defs.lean`) is a second
order linear differential operator.  This module records its *subtractivity*,

  `bslOp α (Ψ - Φ) z θ = bslOp α Ψ z θ - bslOp α Φ z θ`

pointwise at `(z,θ)`, under the standing hypothesis that `Ψ` and `Φ` are `C²` (as functions of
`(z,θ)`) near that point.  As for `Work.Elliptic.bslOp_add`, the `C²` hypothesis is not
decoration: `deriv` in Mathlib is totalised, so `deriv (f - g) = deriv f - deriv g` genuinely
needs differentiability of both summands.

The proof is a one-line reduction to the two linearity facts already available:
`Ψ - Φ = Ψ + (-Φ)` (pointwise), additivity `Work.Elliptic.bslOp_add`, and oddness
`Work.FTS.EllipticEst.bslOp_neg` (which needs no differentiability, `deriv` being totalised).

This is the `Ψ - Φ` companion of `Work.Elliptic.bslOp_add`; it is used to linearise
differences of stream functions (e.g. the difference of two solutions of the same elliptic
problem, or of a solution and the singular model).
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem bslOp_sub (α : ℝ) (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Work.Elliptic.bslOp α (fun z θ => Ψ z θ - Φ z θ) z θ
      = Work.Elliptic.bslOp α Ψ z θ - Work.Elliptic.bslOp α Φ z θ := by
  have hsub : (fun z θ => Ψ z θ - Φ z θ) = fun z θ => Ψ z θ + (-Φ) z θ := by
    funext a b; simp [sub_eq_add_neg]
  rw [hsub, Work.Elliptic.bslOp_add α Ψ (-Φ) z θ hθ hΨ hΦ.neg]
  rw [congrFun (congrFun (bslOp_neg α Φ) z) θ]
  ring

end Work.FTS.EllipticEst
