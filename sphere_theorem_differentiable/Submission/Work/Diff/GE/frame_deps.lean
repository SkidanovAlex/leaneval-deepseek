import Mathlib
import Submission.Work.Diff.GE.frame_family_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Notation-free wrappers for the `frameFamily` development

Delegated statements are elaborated in a file that only gets plain `import`s, so they may not use
scoped notation (`T%`, `∞`, `𝓘(·,·)` are all scoped).  This module collects the few wrappers needed
by the lemma `Work.Diff.GE.exists_ON_frame_family_onFrame` and its supporting lemmas; the scoped
notations are available here, and the wrappers take the manifold data as explicit arguments.

Nothing here is mathematics: `SmoothField X` says that the section `X` is `C^∞`, `SmoothFieldAt X x`
that it is `C^∞` at `x`, and `MDiffAtField X x` that it is differentiable at `x`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- The section `X : Π y, T_yM` is `C^∞`. -/
abbrev SmoothField (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] (X : Π y : M, TangentSpace I y) : Prop :=
  CMDiff ∞ (T% X)

/-- The section `X : Π y, T_yM` is `C^∞` at `x`. -/
abbrev SmoothFieldAt (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] (X : Π y : M, TangentSpace I y) (x : M) : Prop :=
  ContMDiffAt I I.tangent ∞ (T% X) x

/-- The section `X : Π y, T_yM` is differentiable at `x`. -/
abbrev MDiffAtField (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] (X : Π y : M, TangentSpace I y) (x : M) : Prop :=
  MDiffAt (T% X) x

end Work.Diff.GE
