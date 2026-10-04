import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygon.segmentDomain_endpoint_revVelocity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.polygon

open scoped ContDiff Manifold
open Bundle

theorem segmentDomain_at_endpoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x₀ y₀ : M} {r : ℝ} (hr : 0 < r)
    (hinj : Submission.InjRadius.InjAtLeast hmet x₀ r)
    {w : TangentSpace I x₀} (hw : Submission.GlobalExp.GExp (cov := cov) hmet x₀ w = y₀)
    (hd : Manifold.riemannianEDist I x₀ y₀ < ENNReal.ofReal r)
    (hwn : Manifold.riemannianEDist I x₀ y₀ = ENNReal.ofReal ‖w‖) :
    ∃ U : TangentSpace I y₀, ‖U‖ = ‖w‖ ∧
      Submission.GlobalExp.GExp (cov := cov) hmet y₀ U = x₀ ∧
      U ∈ Submission.SegmentDomain.segmentDomain hmet y₀ := by
  classical
  by_cases hw0 : w = 0
  · -- the degenerate case: `y₀ = x₀` and `U = 0`
    subst hw0
    rw [Submission.GlobalExp.GExp_zero] at hw
    subst hw
    refine ⟨0, by simp, by simp, ?_⟩
    exact Submission.SegmentDomain.zero_mem_segmentDomain hmet x₀
  · -- the main case
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hwlt : ‖w‖ < r := by
      have h : ENNReal.ofReal ‖w‖ < ENNReal.ofReal r := by
        rw [← hwn]; exact hd
      exact (ENNReal.ofReal_lt_ofReal_iff').mp h |>.1
    set ξ : TangentSpace I x₀ := Submission.GlobalExp.unitOf w hw0 with hξdef
    have hξ : ‖ξ‖ = 1 := Submission.GlobalExp.unitOf_norm w hw0
    have hξne : ξ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
    have hwsmul : ‖w‖ • ξ = w := by
      rw [hξdef]
      show ‖w‖ • Submission.GlobalExp.unitOf w hw0 = w
      rw [Submission.GlobalExp.unitOf, smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw0), one_smul]
    have hGy : Submission.GlobalExp.GExp (cov := cov) hmet x₀ (‖w‖ • ξ) = y₀ := by
      rw [hwsmul]; exact hw
    subst hGy
    have hspeed : ‖Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) ‖w‖‖ = 1 := by
      rw [Submission.GlobalExp.norm_curveVelocity_GExp_smul hmet x₀ hξne hwpos, hξ]
    refine ⟨‖w‖ • (-(Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) ‖w‖)), ?_, ?_, ?_⟩
    · -- the norm
      rw [smul_neg, Submission.InjRadiusCut.norm_neg_tangent, norm_smul,
        Real.norm_of_nonneg hwpos.le, hspeed, mul_one]
    · -- the reversed ray reaches `x₀`
      rw [Submission.GeodesicLoop.GExp_neg_velocity_of_ray hmet x₀ hξ hwpos
        (s := ‖w‖) hwpos.le le_rfl, sub_self, zero_smul, Submission.GlobalExp.GExp_zero]
    · -- the segment-domain membership
      exact Work.OddBound.polygon.segmentDomain_endpoint_revVelocity
        hmet htor hwpos hwlt hinj hξ

end Work.OddBound.polygon
