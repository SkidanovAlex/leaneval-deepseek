import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.Evol.Vocab

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Second-order data of a frame field

For a family of fields `E : Fin n → Π y, TangentSpace I y` (intended: a frame field which is
*parallel at `x` to first order*, i.e. `∇_v (E i) = 0` for all `v`), the second covariant
derivative of `E i` at `x` is recorded as follows: for vectors `v w : T_xM`, the *canonical*
extensions `smoothExt x v`, `smoothExt x w` are used to form the field-form second derivative
`∇_{smoothExt x v} ∇_{smoothExt x w} (E i)`, paired with `E p x`; `transHess` is the symmetrisation
in `(v,w)` of that pairing.

When `∇(E i) = 0` at `x`, the field-form second derivative depends on the two directions only
through `v` and `w` (the `∇_{∇_vW}` correction carries the factor `∇(E i)`), so `transHess` is the
honest symmetrised Hessian `½(⟪∇²_{v,w}E i, E p x⟫ + ⟪∇²_{w,v}E i, E p x⟫)`.  It is bilinear and
symmetric in `(v,w)`, and — this is the *consistency* used in the construction of the second-order
frame — it is skew in its matrix indices `(p,i)`: `transHess v w p i + transHess v w i p = 0`.
That last identity is the second derivative of the constant function `⟪E i, E p⟫ ≡ δ` along `W`,
expanded with the Leibniz rule `Work.Diff.Evol.mvfderiv_inner_pair_second`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

/-- The symmetrised field-form second derivative of `E i` at `x`, paired with `E p x`. -/
noncomputable def transHess (g : SMet I M) (x : M) {n : ℕ}
    (E : Fin n → Π y : M, TangentSpace I y)
    (v w : TangentSpace I x) (p i : Fin n) : ℝ :=
  (1 / 2) * (g.inner x (lcOf g (fun y : M => lcOf g (E i) y (smoothExt x w y)) x v) (E p x)
    + g.inner x (lcOf g (fun y : M => lcOf g (E i) y (smoothExt x v y)) x w) (E p x))

end Work.Diff.Evol
