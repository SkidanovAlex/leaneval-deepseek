import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.GE.ExtTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the Weitzenböck commutator bound for the tower `∇^k Rm`

Target: `Work.Diff.EXT.lapCovKRm_comm_bound`
(`Submission/Work/Diff/EXT/lapCovKRm_comm_bound.lean`).

`Work.Diff.EXT.lapCovKRm g x (k+1) (Fin.cons w u) a b c d = Σ_m covKRm g x (k+3)
(Fin.cons e_m (Fin.cons e_m (Fin.cons w u))) a b c d` is the rough Laplacian `Δ(∇^{k+1}Rm)`
of `∇^{k+1}Rm`, and `Σ_m covKRm g x (k+3) (Fin.cons w (Fin.cons e_m (Fin.cons e_m u))) a b c d`
is `∇_w(Δ∇^kRm)`.  Their difference is the commutator `[Δ,∇_w]∇^kRm`, a *first order* contraction
of the curvature with the tower and its first derivative, bounded by
`C (|Rm| |∇^{k+1}Rm| + |∇Rm| |∇^kRm|)` times the metric norms of the arguments; after
`2√(xy) ≤ x+y` this is `C (Σ_{j<k+2} f_j)`.

The point of this module is the *only* non-elementary ingredient: the product rule for the
curvature insertion.  Writing `η(U₁,U₂,F)` for `τ` with one slot replaced by the curvature field
`curv cov U₁ U₂ (F s)`, the covariant derivative of `η` in a direction `Z` is the covariant
derivative of `τ` on the modified tuple *plus* `τ` with that slot replaced by the covariant
derivative of the curvature, which is the vector field `dCurvV cov Z U₁ U₂ U` defined below.

The results are:

* `Work.Diff.EXT.extDD_antisymm_gen` (delegated) — the Ricci identity for the `Ext` pattern;
* `Work.Diff.EXT.ckt_swap` (delegated) — the tower swap identity in `ckt` form;
* `Work.Diff.EXT.extD_curvInsertion` (delegated) — the product rule above;
* `Work.Diff.EXT.covKRm_component_le` (delegated) — the component/Frobenius bound;
* `Work.Diff.EXT.dCurvV_norm_le` (delegated) — the norm bound for `dCurvV`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The covariant derivative of the curvature, as a *vector field*: `dCurvV cov Z U₁ U₂ U` is
`(∇_Z curv)(U₁, U₂) U`, i.e. the covariant derivative in the direction `Z` of the `(1,3)`-tensor
field `(U₁,U₂,U) ↦ curv cov U₁ U₂ U`, evaluated on the slots `U₁, U₂, U`.

It is characterised by `⟪dCurvV cov Z U₁ U₂ U, W⟫ = (∇_Z Rm)(U₁,U₂,U,W)`, the fifth derivative
slot `W` being the second curvature slot of `rmP`'s convention
(`rmP g x a b c d = ⟪R(a,b)d, c⟫`). -/
noncomputable def dCurvV (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (Z U₁ U₂ U : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y :=
  fun y => cov (curv cov U₁ U₂ U) y (Z y)
    - curv cov (fun z => cov U₁ z (Z z)) U₂ U y
    - curv cov U₁ (fun z => cov U₂ z (Z z)) U y
    - curv cov U₁ U₂ (fun z => cov U z (Z z)) y

end Work.Diff.EXT
