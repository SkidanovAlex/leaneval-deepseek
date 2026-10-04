import Mathlib
import Submission.Work.Diff.C.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open Bundle CovariantDerivative

/-- **Short geodesic rays from a point are minimising.**  For a non-zero velocity `V` at `x` there
is `ε > 0` such that for every `|s| < ε` the Riemannian distance from `x` to `GExp x (s • V)` is
the Euclidean length `|s| * ‖V‖` of the velocity (i.e. the geodesic ray is minimising up to time
`s`).  This is the local minimality of the exponential map
(`Submission.GlobalExp.exists_pos_riemannianEDist_GExp_smul`), converted into the symmetric
`|s| < ε` form by applying it to the direction `-V` for negative `s`. -/
theorem ray_minimising
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M] [Nontrivial E]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov (⊤ : ℕ∞)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x : M) (V : TangentSpace I x) (hV : V ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| < ε →
      Manifold.riemannianEDist I x (Submission.GlobalExp.GExp hmet x (s • V))
        = ENNReal.ofReal (|s| * ‖V‖) := by
  obtain ⟨ρ, hρ, hkey⟩ :=
    Submission.GlobalExp.exists_pos_riemannianEDist_GExp_smul (I := I) (cov := cov) hmet htor x
  have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hV
  refine ⟨ρ / ‖V‖, div_pos hρ hVpos, fun s hs => ?_⟩
  have hlt : |s| * ‖V‖ < ρ := by
    have h1 : |s| * ‖V‖ < ρ / ‖V‖ * ‖V‖ := mul_lt_mul_of_pos_right hs hVpos
    rwa [div_mul_cancel₀ ρ (ne_of_gt hVpos)] at h1
  rcases lt_or_ge s 0 with hs0 | hs0
  · have habs : |s| = -s := abs_of_neg hs0
    have hcond : (-s) * ‖-V‖ < ρ := by
      rw [norm_neg, ← habs]
      exact hlt
    have h := hkey (-V) (neg_ne_zero.mpr hV) (-s) (by linarith) hcond
    have hsm : (-s) • (-V) = s • V := by rw [smul_neg, neg_smul, neg_neg]
    rw [← hsm, h]
    congr 1
    rw [norm_smul, Real.norm_eq_abs, norm_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ -s), habs]
  · have habs : |s| = s := abs_of_nonneg hs0
    have h := hkey V hV s hs0 (by simpa [habs] using hlt)
    rw [h]
    congr 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]

end Work.Diff.C
