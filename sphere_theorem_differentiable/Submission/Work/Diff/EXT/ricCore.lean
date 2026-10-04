import Mathlib
import Submission.Work.Diff.EXT.ricDeps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `EXT` area: notation-free wrappers for the Ricci-continuity lemmas

The delegated lemmas of the `EXT/ricAt_continuousAt` development are *stated* in a file that only
gets plain `import`s, so their statements may not rely on any scoped notation (`𝓘(·,·)`, `∞`, `T%`
are all scoped notations).  This module collects the few wrappers needed; the scoped notations are
available here, and the wrappers take their manifold data as explicit arguments so that no
typeclass inference is left to chance.

Nothing here is mathematics: `JointSmoothAt I M Φ t₀ x` says `Φ` is jointly `C^∞` near `(t₀, x)`
and `SmoothField I M A` says the section `A` is `C^∞`.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- `Φ : ℝ × M → F` is jointly `C^∞` near `(t₀, x)`. -/
abbrev JointSmoothAt (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (Φ : ℝ × M → F) (t₀ : ℝ) (x : M) : Prop :=
  ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,F) ∞ Φ (t₀, x)

/-- The section `A` is `C^∞`. -/
abbrev SmoothField (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] (A : Π y : M, TangentSpace I y) : Prop :=
  CMDiff ∞ (T% A)

/-- The section `A` is `C^∞` at `x`. -/
abbrev SmoothFieldAt (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] (A : Π y : M, TangentSpace I y) (x : M) : Prop :=
  ContMDiffAt I I.tangent ∞ (T% A) x

end

end Work.Diff.EXT
