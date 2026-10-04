import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- Every time slice `t = σ` of a Ricci flow on `[0,T)` is bounded in the `k`-th curvature norm: the
map `x ↦ |∇^k Rm|²(g(σ))(x)` is continuous (`NormSmoothK`) on the compact manifold `M`. -/
theorem exists_bound_curvNormK_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [CompactSpace M]
    (hreg : Work.Diff.EXT.NormSmoothK (I := I) (M := M))
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hflow : Submission.Diff.IsRicciFlow G T)
    (k : ℕ) {σ : ℝ} (hσ : σ ∈ Set.Ico 0 T) :
    ∃ B : ℝ, ∀ x : M, Work.Diff.EXT.curvNormK (G σ) x k ≤ B := by
  -- The joint smoothness of `(t,x) ↦ |∇^k Rm|²(g(t))(x)` on `Ico 0 T ×ˢ univ` restricts to a
  -- continuous function of `x` on the time slice `t = σ`.
  have hcont : Continuous fun x : M => Work.Diff.EXT.curvNormK (G σ) x k := by
    have h1 := hreg G T hflow k
    have h2 : ContinuousOn (fun p : ℝ × M => Work.Diff.EXT.curvNormK (G p.1) p.2 k)
        (Set.Ico 0 T ×ˢ (Set.univ : Set M)) := h1.continuousOn
    have h3 : ContinuousOn (fun x : M => Work.Diff.EXT.curvNormK (G σ) x k) Set.univ :=
      ContinuousOn.comp (f := fun x : M => (σ, x)) (s := Set.univ)
        (t := Set.Ico 0 T ×ˢ (Set.univ : Set M)) h2
        (continuous_const.prodMk continuous_id).continuousOn
        (fun x _ => ⟨hσ, Set.mem_univ x⟩)
    exact continuousOn_univ.mp h3
  -- A continuous real function on a compact space is bounded above.
  refine ⟨sSup (Set.range fun x : M => Work.Diff.EXT.curvNormK (G σ) x k), fun x => ?_⟩
  exact le_csSup (isCompact_range hcont).bddAbove ⟨x, rfl⟩

end Work.Diff.EXT
