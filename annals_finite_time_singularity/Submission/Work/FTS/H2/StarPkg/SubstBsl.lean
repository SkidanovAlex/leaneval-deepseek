/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `sin θ cos θ`-substitution for `Lzero`

`Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` is the `α = 0` part of the elliptic operator
`bslOp α`, and `sin θ cos θ` is in its kernel.  The substitution `Ξ = sin 2θ · Φ` therefore
turns the elliptic equation into the *divided* form (paper, Proposition `DivisionBySin`):

  `Lzero(sin θ cos θ · w) = -sin θ cos θ·∂_θθw + (3sin²θ - 2cos²θ)·∂_θw`

on `{cos θ ≠ 0}` (in particular on the open quadrant `0 < θ < π/2`, where `IsBslSol` states the
equation).  This is the algebraic layer of the paper's tex-1293 argument, by which the
`z`-derivatives of the divided residual `Φ̃_*/sin 2θ` are traded against the elliptic equation.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.StarPkg

set_option autoImplicit false

/-- First derivative of the substitution: `∂_θ(sin θ cos θ · w) = (cos²θ - sin²θ)·w +
sin θ cos θ·∂_θw`. -/
theorem pth_sin_cos_mul (w : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h1 : DifferentiableAt ℝ (fun θ' => w z θ') θ) :
    Work.Spaces.pth (fun z θ => Real.sin θ * Real.cos θ * w z θ) z θ
      = (Real.cos θ ^ 2 - Real.sin θ ^ 2) * w z θ
        + (Real.sin θ * Real.cos θ) * Work.Spaces.pth w z θ := by
  have ha : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ')
      (Real.cos θ ^ 2 - Real.sin θ ^ 2) θ := by
    have h := (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)
    have he : Real.cos θ * Real.cos θ + Real.sin θ * -Real.sin θ
        = Real.cos θ ^ 2 - Real.sin θ ^ 2 := by ring
    rwa [he] at h
  simp only [Work.Spaces.pth]
  have hfun : (fun θ' : ℝ => Real.sin θ' * Real.cos θ' * w z θ')
      = (fun θ' : ℝ => Real.sin θ' * Real.cos θ') * (fun θ' : ℝ => w z θ') := by
    funext θ'
    rfl
  rw [hfun]
  exact (ha.mul h1.hasDerivAt).deriv

end Work.FTS.H2.StarPkg
