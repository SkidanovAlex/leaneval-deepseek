import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.frame_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `curvDeriv`: the vector `(∇_X curv)(Y,P)Z`, and notation-free wrappers

Delegated statements are elaborated in a file that only gets plain `import`s, so they may not use
scoped notation (`T%`, `∞`, `𝓝`, `𝓘(·,·)` are all scoped).  This module provides

* `curvDeriv g x X Y P Z`, the vector `(∇_X curv)(Y,P)Z` of the covariant derivative of the
  curvature, characterised by `⟪(∇_X curv)(Y,P)Z, Z'⟫ = (∇_X Rm)(Y,P,Z',Z) = covRm g x X Y P Z' Z`;
* the wrapper `OnFrameNear g x E` for "`E` is `g`-orthonormal near `x`".

(`Work.Diff.GE.SmoothField`, from `frame_deps.lean`, is the `C^∞` wrapper for sections.)
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The vector `(∇_X curv)(Y,P) Z` of the covariant derivative of the curvature. -/
noncomputable def curvDeriv (g : SMet I M) (x : M) (X Y P Z : TangentSpace I x) :
    TangentSpace I x :=
  ∑ k, covRm g x X Y P (onFrame g x k) Z • onFrame g x k

/-- `E` is a family of sections that is `g`-orthonormal near `x`. -/
abbrev OnFrameNear (g : SMet I M) (x : M)
    (E : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) : Prop :=
  ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => E i y)

end Work.Diff.GE
