/-
# Difference quotients of a family of functions on `ℍ`

This file sets up the objects used by the quantitative propagation estimate
`Work.CKFinal.dq_propagation`: a family `G r : ℍ → ℂ` of global solutions of the CKMRV
functional equations, and its difference quotients in the family parameter `r`.

The estimate asserts that the difference quotients of `G` in `r` are Cauchy *with a bound
linear in the step sizes*.  The proof propagates the functional equations: the difference of
two difference quotients is again a (holomorphic) solution of the homogeneous second
functional equation, with defect the difference of the corresponding difference quotients of
the inhomogeneity `H`, and the CKMRV propagation bound
`Work.Asymptotics.bound_of_propagates_uniform` converts the bound on `𝒟` into a global
moderate-growth bound.
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.DomainD

noncomputable section

open UpperHalfPlane
open scoped Manifold

namespace Work.CKFinal

/-- The difference quotient `τ ↦ (G (r + s) τ - G r τ)/s` of the family `G` at the base point
`r`, with step `s`. -/
def diffQuot (G : ℝ → ℍ → ℂ) (r s : ℝ) : ℍ → ℂ :=
  fun τ => (G (r + s) τ - G r τ) / s

/-- The second difference of difference quotients, with steps `a` and `b` at base point `r`:
this is the difference quotient of `G` at `r` with step `a` minus the one with step `b`. -/
def dqDiff (G : ℝ → ℍ → ℂ) (r a b : ℝ) : ℍ → ℂ :=
  diffQuot G r a - diffQuot G r b

@[simp] lemma diffQuot_apply (G : ℝ → ℍ → ℂ) (r s : ℝ) (τ : ℍ) :
    diffQuot G r s τ = (G (r + s) τ - G r τ) / s := rfl

@[simp] lemma dqDiff_apply (G : ℝ → ℍ → ℂ) (r a b : ℝ) (τ : ℍ) :
    dqDiff G r a b τ = (G (r + a) τ - G r τ) / a - (G (r + b) τ - G r τ) / b := rfl

end Work.CKFinal
