import Mathlib
import Submission.Work.Diff.L.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Notation-free vocabulary for the statements of the `Work.Diff.L` delegated lemmas

The pipeline that checks (and files) a delegated lemma statement elaborates that statement in a file
that receives only **plain `import`s**, so the statement may not use any scoped notation
(`∞`, `T%`, `𝓘(·,·)`, `∀ᶠ`, `𝓝`, `ᵀ`, ...).  This module provides plain-name `abbrev`s (defined
here, where the scoped notations *are* available) for the notions used by the delegated statements of
this area.

Everything here is definitional: `SmoothField A` is `CMDff ∞ (T% A)`, `SmoothFun u` is
`CMDiff ∞ u` for a real-valued function, and `ONFrameNear g x F` is
`∀ᶠ y in 𝓝 x, IsONFrame g y (F y)`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.L

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A tangent-bundle section is `C^∞` (plain-name form of `CMDiff ∞ (T% A)`). -/
abbrev SmoothField [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    (A : Π y : M, TangentSpace I y) : Prop := CMDiff ∞ (T% A)

/-- A tangent-bundle section is `C^∞` at `x` (plain-name form of `CMDiffAt ∞ (T% A) x`). -/
abbrev SmoothFieldAt [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    (A : Π y : M, TangentSpace I y) (x : M) : Prop := CMDiffAt ∞ (T% A) x

/-- A real-valued function on `M` is `C^∞` (plain-name form of `CMDiff ∞ u`).  The manifold data is
passed explicitly because the function alone does not determine it. -/
abbrev SmoothFun (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] (u : M → ℝ) : Prop := CMDiff ∞ u

/-- The family `F` consists of `g`-orthonormal frames near `x`
(plain-name form of `∀ᶠ y in 𝓝 x, IsONFrame g y (F y)`). -/
abbrev ONFrameNear [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    (g : SMet I M) (x : M) (F : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y) : Prop :=
  ∀ᶠ y in 𝓝 x, IsONFrame g y (F y)

end Work.Diff.L
