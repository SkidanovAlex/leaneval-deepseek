import Mathlib
import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

theorem reeb_field_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {V : (x : M) → TangentSpace I x}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I)))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, ‖V x‖ ≤ C := by
  classical
  -- The fibrewise pairing `⟪V, V⟫` is smooth because the bundle is a smooth Riemannian bundle.
  have hsmooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      (fun x : M => Inner.inner ℝ (V x) (V x)) :=
    ContMDiff.inner_bundle (F := E) (E := fun x : M => TangentSpace I x) (b := id)
      (v := V) (w := V) hVsm hVsm
  -- Hence the norm `x ↦ ‖V x‖`, being its square root, is continuous.
  have hcont : Continuous (fun x : M => ‖V x‖) := by
    refine (hsmooth.continuous.sqrt).congr (fun x => ?_)
    exact (norm_eq_sqrt_real_inner (V x)).symm
  -- A continuous real function on a compact space is bounded above.
  obtain ⟨C, hC⟩ := (isCompact_range hcont).bddAbove
  exact ⟨max C 0, le_max_right _ _, fun x => le_trans (hC ⟨x, rfl⟩) (le_max_left _ _)⟩

end Work.Diff.Dim2
