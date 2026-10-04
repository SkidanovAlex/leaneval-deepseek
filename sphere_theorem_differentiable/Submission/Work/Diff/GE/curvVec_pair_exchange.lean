import Mathlib
import Submission.Work.Diff.GE.bianchi_kato_defs
import Submission.Work.Diff.GE.curvVec_bianchi_nb

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.GE Submission.CurvatureVec

section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The cyclic relation `(*)`: pairing the first Bianchi identity with `z` and using the
skew-symmetry in the last two slots twice gives
`S(u,v,w,z) = S(v,w,z,u) + S(w,u,z,v)`. -/
private theorem curvVec_cyclic_aux
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (htor : cov.torsion = 0)
    (hmet : IsMetricCompatible cov) (x : M) (u v w z : TangentSpace I x) :
    inner ℝ (curvVec cov x u v w) z
      = inner ℝ (curvVec cov x v w z) u + inner ℝ (curvVec cov x w u z) v := by
  have hb := curvVec_bianchi_nb cov hcov htor x u v w
  have h := congrArg (fun t : TangentSpace I x => inner ℝ t z) hb
  simp only [inner_add_left, inner_zero_left] at h
  have h1 : inner ℝ (curvVec cov x v w u) z = - inner ℝ (curvVec cov x v w z) u := by
    rw [inner_curvVec_skew cov hcov hmet x v w u z, real_inner_comm u (curvVec cov x v w z)]
  have h2 : inner ℝ (curvVec cov x w u v) z = - inner ℝ (curvVec cov x w u z) v := by
    rw [inner_curvVec_skew cov hcov hmet x w u v z, real_inner_comm v (curvVec cov x w u z)]
  linarith

end Aux

/-- **Exchange of the two pairs of the curvature pairing.** With `R := curvVec cov` (the pointwise
curvature of `cov`): `⟪R(u,v)w, z⟫ = ⟪R(w,z)u, v⟫`.

Why this is wanted: the curvature components of a metric in a frame, `R i j k l = ⟪R(eᵢ,eⱼ)e_l, e_k⟫`,
form an algebraic curvature array; this pair exchange is the one non-immediate ingredient (the other
components are `curvVec_antisymm`, `inner_curvVec_skew` and the Bianchi identity).

Inputs available in this workspace.  Write `S(X,Y,Z,W) := ⟪R(X,Y)Z, W⟫`.  It is enough to have
(A) `curvVec_antisymm` : `R(X,Y)W = -R(Y,X)W`  (so `S(X,Y,Z,W) = -S(Y,X,Z,W)`);
(B) `inner_curvVec_skew` (needs `hmet`) : `⟪R(X,Y)Z, W⟫ = -⟪Z, R(X,Y)W⟫`, which with
    `real_inner_comm` gives antisymmetry in the last two slots;
(C) the first Bianchi identity (needs `hcov`, `htor`) `R(x,y)z + R(y,z)x + R(z,x)y = 0`; pairing it
    with `W` and using (B) twice gives  `S(X,Y,Z,W) = S(Y,Z,W,X) + S(Z,X,W,Y)`.                (*)
For (C): do NOT use `Submission.CurvatureSym.curvVec_bianchi` -- it carries a spurious
`[I.Boundaryless]` typeclass hypothesis, which is not available here.  Use instead the sibling module
`Submission.Work.Diff.GE.curvVec_bianchi_nb`, which provides exactly this Boundaryless-free Bianchi
identity as `Work.Diff.GE.curvVec_bianchi_nb` (it is in `depends_on`).

Proof to formalize.  From (*) applied to `(X,Y,Z,W)`, and (*) again to each of its two summands,
`S(X,Y,Z,W) = S(Z,W,X,Y) + S(W,Y,X,Z) + S(X,W,Y,Z) + S(W,Z,Y,X)`.                               (**)
Here `S(W,Z,Y,X) = S(Z,W,X,Y)` by (A) then (B), and (*) on `(W,Y,X,Z)` together with (A) and (B)
gives `S(W,Y,X,Z) = -S(X,Y,Z,W) - S(X,W,Y,Z)`.  Substituting the last two relations in (**) yields
`S(X,Y,Z,W) = 2 * S(Z,W,X,Y) - S(X,Y,Z,W)`; `linarith` then concludes the goal `S(X,Y,Z,W) =
S(Z,W,X,Y)`.

Consistency: when the first pair is degenerate both sides vanish, so there is no edge-case
obstruction; a brute-force exact linear algebra check confirms that (A)+(B)+Bianchi force exactly
this pair exchange (the Bianchi kernel inside `Λ² ⊗ Λ²` is the space of algebraic curvature arrays,
of dimension `n²(n²−1)/12` for `n = 2,3,4,5`). -/
theorem curvVec_pair_exchange
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (htor : cov.torsion = 0)
    (hmet : IsMetricCompatible cov) (x : M) (u v w z : TangentSpace I x) :
    inner ℝ (curvVec cov x u v w) z = inner ℝ (curvVec cov x w z u) v := by
  -- (*) in the four instantiations needed for the (**) expansion
  have k1 := curvVec_cyclic_aux cov hcov htor hmet x u v w z
  have k2 := curvVec_cyclic_aux cov hcov htor hmet x v w z u
  have k3 := curvVec_cyclic_aux cov hcov htor hmet x w u z v
  have k4 := curvVec_cyclic_aux cov hcov htor hmet x z v u w
  -- (A): `S(z,w,v,u) = S(w,z,u,v)`, i.e. `S(W,Z,Y,X) = S(Z,W,X,Y)`
  have hA2 : inner ℝ (curvVec cov x z w v) u = - inner ℝ (curvVec cov x w z v) u := by
    rw [curvVec_antisymm cov hcov x z w v, inner_neg_left]
  have hB1 : inner ℝ (curvVec cov x w z v) u = - inner ℝ (curvVec cov x w z u) v := by
    rw [inner_curvVec_skew cov hcov hmet x w z v u, real_inner_comm v (curvVec cov x w z u)]
  -- (B): `S(z,v,u,w) = -S(u,v,w,z) - S(u,z,v,w)`
  have hA1 : inner ℝ (curvVec cov x v u w) z = - inner ℝ (curvVec cov x u v w) z := by
    rw [curvVec_antisymm cov hcov x v u w, inner_neg_left]
  have hB2 : inner ℝ (curvVec cov x u z w) v = - inner ℝ (curvVec cov x u z v) w := by
    rw [inner_curvVec_skew cov hcov hmet x u z w v, real_inner_comm w (curvVec cov x u z v)]
  linarith

end Work.Diff.GE
