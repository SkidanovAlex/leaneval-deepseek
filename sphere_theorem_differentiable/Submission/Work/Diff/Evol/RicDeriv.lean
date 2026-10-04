import Mathlib
import Submission.Diff.Evol

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Covariant derivatives of the Ricci tensor (definitions)

The frozen modules give the curvature components `rmP g x a b c d = g(R(a,b)d,c)` and its covariant
derivatives `covRm`, `cov2Rm` (`Submission.Diff.Grad`, `Submission.Diff.Evol`), but not the covariant
derivatives of the Ricci tensor `ricAt (lcOf g) x · ·`.  They are the "`Ext` pattern" objects

`covRic g x v a b = (∇_v Ric)(a,b) = ∂_v(Ric(a,b)) - Ric(∇_v a, b) - Ric(a, ∇_v b)`

and its covariant derivative, with the derivatives taken with the `Classical.epsilon`-chosen
extensions `smoothExt x ·` (the same convention as `covRm`).

These are the objects in which the fixed-vector form of Hamilton's evolution equation reads

  `∂ₜ ⟨R(a,b)d,c⟩ = (ΔR)(a,b,c,d) - Q̂(R)(a,b,c,d) + ricact(R)(a,b,c,d)`

with `Q̂`, `ricact` the arrays of `Submission/Work/Diff/Evol/Calc.lean`.
-/

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `(∇_v Ric)(a,b)` computed with the chosen smooth extensions of the three vectors. -/
noncomputable def covRic (g : SMet I M) (x : M) (v a b : TangentSpace I x) : ℝ :=
  mvfderiv I (fun y : M ↦ ricAt (lcOf g) y (smoothExt x a y) (smoothExt x b y)) x v
    - ricAt (lcOf g) x (lcOf g (smoothExt x a) x v) b
    - ricAt (lcOf g) x a (lcOf g (smoothExt x b) x v)

/-- `(∇_v∇_w Ric)(a,b)`, the second covariant derivative of the Ricci tensor. -/
noncomputable def cov2Ric (g : SMet I M) (x : M) (v w a b : TangentSpace I x) : ℝ :=
  mvfderiv I (fun y : M ↦ covRic g y (smoothExt x w y) (smoothExt x a y) (smoothExt x b y)) x v
    - covRic g x (lcOf g (smoothExt x w) x v) a b
    - covRic g x w (lcOf g (smoothExt x a) x v) b
    - covRic g x w a (lcOf g (smoothExt x b) x v)

end Work.Diff.Evol
