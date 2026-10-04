import Mathlib
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Area C: every point is reached by a geodesic ray from `p`

`ray_cover` is the "covering" half of the classical endgame's use of the exponential map: for
`x ≠ p` there is a *unit* vector `u ∈ T_pM` and a time `s > 0` with

  `s = d(p,x)`,  `GExp p (s • u) = x`.

It is an immediate consequence of Hopf–Rinow (`Submission.HopfRinow.exists_geodesic_riemannianEDist_eq`),
which produces `v ∈ T_pM` with `GExp p v = x` and `d(p,x) = ‖v‖`; one takes `s = ‖v‖` and
`u = unitOf v` (`v ≠ 0` because `x ≠ p`).  The only bookkeeping is the passage between the
extended distance `Manifold.riemannianEDist` and the real-valued `rdist = ·.toReal`.
-/

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem ray_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (p : M) {x : M} (hx : x ≠ p) :
    ∃ (u : TangentSpace I p) (s : ℝ), Inner.inner ℝ u u = 1 ∧ 0 < s ∧
      rdist (I := I) (M := M) p x = s ∧
      Submission.GlobalExp.GExp (cov := cov) hmet p (s • u) = x := by
  haveI hreg : RegularSpace M := inferInstance
  -- Hopf–Rinow: a minimising geodesic from `p` to `x`.
  obtain ⟨v, hvx, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor p x
  -- `v ≠ 0`, otherwise `GExp p 0 = p`, contradicting `x ≠ p`.
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, Submission.GlobalExp.GExp_zero] at hvx
    exact hx hvx.symm
  refine ⟨Submission.GlobalExp.unitOf v hvne, ‖v‖, ?_, ?_, ?_, ?_⟩
  · -- unit vector
    rw [real_inner_self_eq_norm_sq, Submission.GlobalExp.unitOf_norm]
    norm_num
  · -- positive time
    exact norm_pos_iff.mpr hvne
  · -- the time is the distance
    show (Manifold.riemannianEDist I p x).toReal = ‖v‖
    rw [hvd, ENNReal.toReal_ofReal (norm_nonneg v)]
  · -- the ray reaches `x`
    show Submission.GlobalExp.GExp (cov := cov) hmet p
      (‖v‖ • Submission.GlobalExp.unitOf v hvne) = x
    rw [Submission.GlobalExp.unitOf, smul_smul,
      mul_inv_cancel₀ (by simpa [norm_eq_zero] using hvne), one_smul]
    exact hvx

end Work.Diff.C
