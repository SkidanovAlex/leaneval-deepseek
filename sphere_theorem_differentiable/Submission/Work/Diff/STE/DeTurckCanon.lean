/-
# The DeTurck field is canonical (frame-free) — corollaries of `traceVec_eq_sum_invGram`

`Work.Diff.STE.DeTurck.deTurckVec g gbar` is *defined* frame-freely (as
`traceVec (connDiff g gbar x)`, with `traceVec` built from Mathlib's `LinearMap.trace` and the
Riesz isomorphism), so it is automatically independent of any choice of frame.  This file records
the consequence that makes it *computable*: the trace can be evaluated in **any** basis, and the two
expressions agree.

This is the ingredient that lets the DeTurck field be used simultaneously in all charts of an
atlas: a chartwise formula would give *different* fields in different charts, and the local
solutions of the gauge-modified equation would then solve different equations and could not be
glued by uniqueness.
-/

import Mathlib
import Submission.Work.Diff.STE.DeTurckField
import Submission.Work.Diff.STE.deTurck.traceVec_eq_sum_invGram

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Work.Diff.STE.DeTurck

namespace Work.Diff.STE.DeTurck

/-- The trace of `S : V →L[ℝ] V →L[ℝ] V` with respect to the inner product, evaluated in a basis:
`∑_{ij} γ^{ij} S (b i) (b j)` where `γ` is the inverse Gram matrix of `b`. -/
noncomputable def traceInBasis {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : V →L[ℝ] V →L[ℝ] V)
    (b : Module.Basis ι ℝ V) : V :=
  ∑ i, ∑ j, ((Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹) i j • S (b i) (b j)

/-- **The frame-independent trace formula**: the trace of `S` is `traceInBasis S b` for every
basis `b`. -/
theorem traceVec_eq_traceInBasis {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [CompleteSpace V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : V →L[ℝ] V →L[ℝ] V)
    (b : Module.Basis ι ℝ V) : traceVec S = traceInBasis S b := by
  rw [traceInBasis, Work.Diff.STE.deTurck.traceVec_eq_sum_invGram S b]

/-- **The trace does not depend on the basis**: the expressions `traceInBasis S b` agree for any two
bases of `V`. -/
theorem traceInBasis_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [CompleteSpace V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : V →L[ℝ] V →L[ℝ] V)
    (b b' : Module.Basis ι ℝ V) : traceInBasis S b = traceInBasis S b' := by
  rw [← traceVec_eq_traceInBasis S b, ← traceVec_eq_traceInBasis S b']

end Work.Diff.STE.DeTurck
