import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.EXT.rmP_pair_symm
import Submission.Work.EXT.ricAt_eq_sum_frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Symmetry of the pointwise Ricci tensor of a Levi-Civita connection

`Submission.Diff.ricAt (lcOf g) x u v` is the Ricci tensor of the smooth metric `g` at `x`, defined
as the trace `tr (w ↦ R(w,u)v)` of the pointwise curvature in the canonical basis of the model
space.  This file proves that it is symmetric in its two vector arguments:

`ricAt (lcOf g) x u v = ricAt (lcOf g) x v u`.

## The mathematics

Let `R` be the curvature of the Levi-Civita connection, with the convention
`⟪R(X,Y)Z,W⟫ = R_{XYZW}`, so that the pair-exchange symmetry of the Riemannian curvature tensor reads

`⟪R(X,Y)Z, W⟫ = ⟪R(Z,W)X, Y⟫`                                                          (PE)

(equivalently `R_{abcd} = R_{cdab}`; it follows from the first Bianchi identity together with
antisymmetry in the first pair, which in turn comes from metric compatibility and `R(X,Y)Z =
-R(Y,X)Z`).

For a `g`-orthonormal frame `e` of `TₓM`, the trace of `w ↦ R(w,u)v` is also the metric trace

`Ric(u,v) = ∑_j ⟪R(e_j,u)v, e_j⟫`

— the basis-independence of the trace of an endomorphism
(`Work.EXT.ricAt_eq_sum_frame`, an instance-free restatement of `ricAt_eq_sum_frame`).  Applying the
pair exchange (PE) with `(X,Y,Z,W) = (e_j,u,e_j,v)` turns each summand into
`⟪R(e_j,v)u, e_j⟫`, whence `Ric(u,v) = Ric(v,u)`: the trace is unchanged term by term.  This is the
classical proof of the symmetry of the Ricci tensor.

In the frozen vocabulary of the workspace, the pairing `⟪R(a,b)d, c⟫` is `Submission.Diff.rmP g x a b c d`
and (PE) in this index convention is exactly `rmP g x a b c d = rmP g x c d a b`
(`Work.EXT.rmP_pair_symm`, proved in `Submission/Work/EXT/rmP_pair_symm.lean` from the Bianchi
identity, antisymmetry in the first pair and skew-adjointness in the last pair of `lcOf g`).

Note (reuse): the same statement is available as `Work.Diff.EXT.ricAt_symm_L`
(`Submission/Work/Diff/EXT/ric_bound_of_curvBound.lean`), which carries the (redundant) additional
hypothesis `ContMDiffCovariantDerivative (lcOf g) ∞`; here it is derived from the frozen contract
`LCSmooth I M` alone, and the proof below is self-contained with respect to the two lemmas quoted
above.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

theorem ricAt_symm_kit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (u v : TangentSpace I x) :
    Submission.Diff.ricAt (Submission.Diff.lcOf g) x u v
      = Submission.Diff.ricAt (Submission.Diff.lcOf g) x v u := by
  -- the Levi-Civita connection of `g` is smooth (first component of the frozen contract)
  have hcov : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ := (hLC g).1.some
  -- an orthonormal frame of `TₓM` exists for every metric
  have he : Submission.Diff.IsONFrame g x (Submission.Diff.onFrame g x) :=
    Work.Diff.GE.isONFrame_onFrame g x
  -- read both traces in that frame
  rw [Work.EXT.ricAt_eq_sum_frame g hcov x (Submission.Diff.onFrame g x) he u v,
    Work.EXT.ricAt_eq_sum_frame g hcov x (Submission.Diff.onFrame g x) he v u]
  -- each summand is the other summand by the pair-exchange symmetry of the curvature
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa only [Submission.Diff.rmP] using
    Work.EXT.rmP_pair_symm hLC g x (Submission.Diff.onFrame g x j) u
      (Submission.Diff.onFrame g x j) v

end Work.Diff.GE
