import Mathlib
import Submission.Diff.Evol

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the `Evol` area (LapRmFrameParallel)

Delegated lemmas are elaborated in a file that only receives plain `import`s, so their statements
may not use scoped notation (`T%`, `∞`, `𝓝` are all scoped).  The abbreviations below let such a
statement be written without any scoped notation, while still being readable.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The section `X : Π y, T_yM` is `C^∞`. -/
abbrev SmoothField (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (X : Π y : M, TangentSpace I y) : Prop :=
  CMDiff ∞ (T% X)

/-- The section `X : Π y, T_yM` is `C^∞` on the set `s`. -/
abbrev SmoothFieldOn (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (X : Π y : M, TangentSpace I y) (s : Set M) : Prop :=
  ContMDiffOn I I.tangent ∞ (T% X) s

/-- A family of `C^∞` sections `Ef` is `g`-orthonormal near `x`. -/
abbrev ONFrameNear (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (g : SMet I M) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y) : Prop :=
  ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i ↦ Ef i y)

/-- A family of `C^∞` sections `Ef` is `g`-orthonormal at `x`. -/
abbrev ONFrameAt (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (g : SMet I M) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y) : Prop :=
  IsONFrame g x (fun i ↦ Ef i x)

/-- The family `Ef` is `C^∞` and takes the prescribed values `e` at `x`. -/
abbrev SharpAt (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y) : Prop :=
  (∀ i, Ef i x = e i) ∧ ∀ i, SmoothField I M (Ef i)

/-- A map `B : M → F` into a normed space is `C^∞`. -/
abbrev SmoothMap (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : M → F) : Prop := CMDiff ∞ B

end Work.Diff.Evol
