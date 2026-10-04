import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.Evol.RicDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `EXT` area: notation-free wrappers for the connection-difference estimate

Delegated statements are elaborated in a file that only gets plain `import`s, so they may not use
scoped notation (`T%`, `∞`, `𝓘(·,·)` are all scoped).  This module collects the wrappers needed by
the lemmas of the `conn_diff_bound_of_LV` development.

Nothing here is mathematics: `SmoothField X` says the section `X` is `C^∞`.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The section `X : Π y, T_yM` is `C^∞`.

The name is `SmoothFieldC` (rather than `SmoothField`) to avoid a clash with the identically named
abbreviation `Work.Diff.EXT.SmoothField (I) (M) (A)` of `Submission/Work/Diff/EXT/ricCore.lean`:
two declarations of the same name in the same namespace cannot be imported together, and the
`ConnDefs`-branch and the `ricCore`-branch of the `EXT` development must coexist in the files that
assemble them. -/
abbrev SmoothFieldC (X : Π y : M, TangentSpace I y) : Prop := CMDiff ∞ (T% X)



open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The covariant derivative `cov` is smooth (notation-free form of
`ContMDiffCovariantDerivative cov ∞`). -/
abbrev CovSmooth (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  Nonempty (ContMDiffCovariantDerivative cov ∞)

end Work.Diff.EXT
