import Mathlib
import Submission.Diff.Evol
import Submission.Diff.Alg
import Submission.Diff.Interfaces
import Submission.Work.Diff.MP.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Notation-free wrappers for the MP area

Delegated statements are elaborated in a file that only gets plain `import`s, so they may not use
scoped notation (`T%`, `∞`, `𝓘(·,·)`, `𝓝` are all scoped) and cannot rely on `open` commands.
This module collects the few wrappers needed by the delegated lemmas of the `MP` area
(Hamilton's maximum principle for time-dependent invariant families).

Nothing here is mathematics:
* `SmField I M X` says that the section `X : Π y, T_yM` is `C^∞`;
* `growRad ϱ Λ s = ϱ / (1 - Λ s)` is the radius of the growing truncation ball used to make the
  one-Euler-step push-forward of the ODE `R' = Q(R)` stay inside the truncated family;
* `truncFam F ϱ Λ a t = F t ∩ frobBall (growRad ϱ Λ (t - a))` is the truncated family at time `t`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.MP

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The section `X : Π y, T_yM` is `C^∞`. -/
abbrev SmField (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (X : Π y : M, TangentSpace I y) : Prop := CMDiff ∞ (T% X)

/-- The radius of the growing truncation ball, `ϱ / (1 - Λ s)`.  It solves `Υ' = Λ Υ²` with
`Υ 0 = ϱ`, hence dominates the growth of the one-step push-forward of `R' = Q(R)` on the ball. -/
noncomputable def growRad (ϱ Λ s : ℝ) : ℝ := ϱ / (1 - Λ * s)

/-- The truncated family `F t ∩ frobBall (growRad ϱ Λ (t - a))`. -/
noncomputable def truncFam {n : ℕ} (F : ℝ → Set (Curv4 n)) (ϱ Λ a t : ℝ) : Set (Curv4 n) :=
  F t ∩ frobBall (growRad ϱ Λ (t - a))

@[simp] theorem truncFam_eq {n : ℕ} (F : ℝ → Set (Curv4 n)) (ϱ Λ a t : ℝ) :
    truncFam F ϱ Λ a t = F t ∩ frobBall (growRad ϱ Λ (t - a)) := rfl

end Work.Diff.MP
