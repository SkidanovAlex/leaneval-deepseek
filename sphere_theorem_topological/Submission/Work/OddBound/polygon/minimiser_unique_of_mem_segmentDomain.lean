import Mathlib
import Submission.Work.OddBound.LiftKit

namespace Work.OddBound.polygon

open scoped ContDiff Manifold
open Bundle

/-- Uniqueness of the minimising vector from `q` to `p` when the ray of `U` is *strictly* minimising
at `‖U‖` (i.e. `U` lies in the tangential segment domain `D̃_q`).  Standard proof: if `V ≠ U` were
another minimising vector of the same length, the two rays would be distinct minimising rays of the
same length meeting at `p`, so `cutTime_le_of_meet` gives `cutTime q (unitOf U) ≤ ‖U‖`, contradicting
`‖U‖ < cutTime q (unitOf U)` from `hseg`. -/
theorem minimiser_unique_of_mem_segmentDomain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {U : TangentSpace I q} (hU : U ≠ 0)
    (hseg : U ∈ Submission.SegmentDomain.segmentDomain hmet q)
    {p : M} (hUp : Submission.GlobalExp.GExp (cov := cov) hmet q U = p)
    {V : TangentSpace I q} (hV : Submission.GlobalExp.GExp (cov := cov) hmet q V = p)
    (hVn : ‖V‖ = ‖U‖) : V = U := by
  classical
  -- from `U ∈ D̃_q` and `U ≠ 0`: strict minimality of the ray of `U` at `‖U‖`
  obtain ⟨hUne, hult⟩ :=
    ((Submission.SegmentDomain.mem_segmentDomain_iff hmet q U).mp hseg).resolve_left hU
  -- the ray of `U` is minimising at time `‖U‖`
  have hminU : Manifold.riemannianEDist I q (Submission.GlobalExp.GExp (cov := cov) hmet q U)
      = ENNReal.ofReal ‖U‖ :=
    Submission.SegmentDomain.edist_GExp_eq_norm_of_mem_segmentDomain hmet htor hseg
  -- `V ≠ 0` as well
  have hVne : V ≠ 0 := by
    intro h0
    exact hU (norm_eq_zero.mp (by rw [← hVn, h0, norm_zero]))
  -- rescaling both vectors to their common length `‖U‖ = ‖V‖`
  have key : ‖U‖ • Submission.GlobalExp.unitOf U hUne = U := by
    rw [Submission.GlobalExp.unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hUne), one_smul]
  have key' : ‖U‖ • Submission.GlobalExp.unitOf V hVne = V := by
    rw [Submission.GlobalExp.unitOf, smul_smul, ← hVn,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hVne), one_smul]
  -- the common endpoint is at distance `‖U‖`
  have hpt : Manifold.riemannianEDist I q p = ENNReal.ofReal ‖U‖ := by
    rw [← hUp]; exact hminU
  by_cases hdir : Submission.GlobalExp.unitOf U hUne = Submission.GlobalExp.unitOf V hVne
  · -- same unit direction: both vectors are the same multiple of it
    calc V = ‖U‖ • Submission.GlobalExp.unitOf V hVne := key'.symm
      _ = ‖U‖ • Submission.GlobalExp.unitOf U hUne := by rw [hdir]
      _ = U := key
  · -- distinct directions: two distinct minimising rays of the same length meet at `p`
    have hξ : ‖Submission.GlobalExp.unitOf U hUne‖ = 1 :=
      Submission.GlobalExp.unitOf_norm U hUne
    have hη : ‖Submission.GlobalExp.unitOf V hVne‖ = 1 :=
      Submission.GlobalExp.unitOf_norm V hVne
    have hmeet : Submission.GlobalExp.GExp (cov := cov) hmet q
        (‖U‖ • Submission.GlobalExp.unitOf U hUne)
        = Submission.GlobalExp.GExp (cov := cov) hmet q
          (‖U‖ • Submission.GlobalExp.unitOf V hVne) := by
      rw [key, key', hUp, hV]
    have hξmin : Manifold.riemannianEDist I q
        (Submission.GlobalExp.GExp (cov := cov) hmet q
          (‖U‖ • Submission.GlobalExp.unitOf U hUne)) = ENNReal.ofReal ‖U‖ := by
      rw [key]; exact hminU
    have hηmin : Manifold.riemannianEDist I q
        (Submission.GlobalExp.GExp (cov := cov) hmet q
          (‖U‖ • Submission.GlobalExp.unitOf V hVne)) = ENNReal.ofReal ‖U‖ := by
      rw [key', hV]; exact hpt
    have hle := Submission.SegmentDomain.cutTime_le_of_meet (cov := cov) hmet htor
      (p := q) (m := ‖U‖) hξ hη hdir (norm_pos_iff.mpr hUne) hξmin hηmin hmeet
    exact absurd hle (not_le.mpr hult)

end Work.OddBound.polygon
