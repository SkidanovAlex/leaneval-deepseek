import Mathlib
import Submission.Work.Diff.EXT.evolX.connVarDefs
import Submission.Work.Diff.EXT.curvNormK_jointSmooth
import Submission.Work.Diff.T.lc_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity at the initial time of the reaction shape times metric norms

`Shape (G t) x m = ∑_{i ≤ m} √(f_i) √(f_{m−i})` with `f_i = curvNormK (G t) x i = |∇^i Rm|²` is the
sharp shape of the reaction estimate of the `k`-th order Shi estimate, and the factor
`∏ r, √((G t).inner x (w r) (w r))` is the product of the metric norms of the vectors at which the
estimate is evaluated.  This module proves that this product of quantities is continuous at the
initial time `t = 0` within `[0,T)`, along a Ricci flow `G` on `[0,T)`.

## Route

* `t ↦ (G t).inner x u v` is continuous within `[0,T)` at `0` because its derivative within the
  interval exists (`IsRicciFlow`), so `t ↦ √((G t).inner x (w r) (w r))` is too (continuous
  composition with `Real.sqrt`), and then so is the finite product (`tendsto_finsetProd`).
* For `Shape` it suffices that `t ↦ curvNormK (G t) x k` is continuous within `[0,T)` at `0` for
  every `k`.  This is the *slice at* `x` of the joint smoothness of `(t,y) ↦ curvNormK (G t) y k`
  along the flow, which is the interface `Work.Diff.EXT.NormSmoothK`, proved in
  `Submission/Work/Diff/EXT/curvNormK_jointSmooth.lean` from the smoothness of the Levi-Civita
  connection (`Work.Diff.T.lc_smooth`, contract T1) and the frame-independence of
  `∑ (components of ∇^k Rm)²`.  Restricting the `ContinuousOn` statement along the continuous map
  `t ↦ (t,x)` and using `ContinuousOn.continuousWithinAt` gives the claim.
* The degenerate case `T ≤ 0` is vacuous (`[0,T) = ∅`).
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

/-- **Continuity at `0` of the `k`-th curvature norm along a Ricci flow.**

This is the time-slice at `x` of the joint smoothness of `(t,y) ↦ curvNormK (G t) y k` on
`Ico 0 T ×ˢ univ` (`Work.Diff.EXT.curvNormK_jointSmooth`). -/
theorem curvNormK_continuousWithinAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    (x : M) (k : ℕ) :
    ContinuousWithinAt (fun t : ℝ => Work.Diff.EXT.curvNormK (G t) x k) (Set.Ico 0 T) 0 := by
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    have hmem : (0 : ℝ) ∈ Set.Ico 0 T := ⟨le_refl 0, hTpos⟩
    have hLC : Submission.Diff.LCSmooth I M := Work.Diff.T.lc_smooth (I := I) (M := M)
    have hjoint := Work.Diff.EXT.curvNormK_jointSmooth (I := I) (M := M) hLC G T hflow k
    have hcontOn : ContinuousOn (fun t : ℝ => Work.Diff.EXT.curvNormK (G t) x k)
        (Set.Ico 0 T) :=
      ContinuousOn.comp
        (f := fun t : ℝ => (t, x))
        (s := Set.Ico 0 T) (t := Set.Ico 0 T ×ˢ (Set.univ : Set M))
        (g := fun p : ℝ × M => Work.Diff.EXT.curvNormK (G p.1) p.2 k)
        hjoint.continuousOn ((continuous_id.prodMk continuous_const).continuousOn)
        (fun t0 ht0 => ⟨ht0, Set.mem_univ x⟩)
    exact hcontOn.continuousWithinAt hmem

/-- **Continuity at `0` of a square root of a curvature norm along a Ricci flow.** -/
theorem sqrt_curvNormK_continuousWithinAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    (x : M) (k : ℕ) :
    ContinuousWithinAt (fun t : ℝ => Real.sqrt (Work.Diff.EXT.curvNormK (G t) x k))
      (Set.Ico 0 T) 0 :=
  (Real.continuous_sqrt.continuousWithinAt).comp
    (curvNormK_continuousWithinAt_zero (I := I) (M := M) hflow x k)
    (fun _ _ => Set.mem_univ _)

/-- **Continuity at `0` of a metric pairing along a Ricci flow.** -/
theorem inner_continuousWithinAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    (x : M) (u v : TangentSpace I x) :
    ContinuousWithinAt (fun t : ℝ => (G t).inner x u v) (Set.Ico 0 T) 0 := by
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · exact ((hflow.2 0 ⟨le_refl 0, not_le.mp hT⟩ x u v).continuousWithinAt)

/-- **Continuity at `0` of the reaction shape `Shape (G t) x m` along a Ricci flow.** -/
theorem shape_continuousWithinAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    (x : M) (m : ℕ) :
    ContinuousWithinAt (fun t : ℝ => Work.Diff.EXT.Shape (G t) x m) (Set.Ico 0 T) 0 := by
  have hfun : (fun t : ℝ => Work.Diff.EXT.Shape (G t) x m)
      = fun t : ℝ => ∑ i ∈ Finset.range (m + 1),
          Real.sqrt (Work.Diff.EXT.curvNormK (G t) x i)
            * Real.sqrt (Work.Diff.EXT.curvNormK (G t) x (m - i)) := by
    funext t
    rw [Work.Diff.EXT.Shape]
  rw [hfun]
  exact tendsto_finsetSum (Finset.range (m + 1)) (fun i _ =>
    ((sqrt_curvNormK_continuousWithinAt_zero (I := I) (M := M) hflow x i).mul
      (sqrt_curvNormK_continuousWithinAt_zero (I := I) (M := M) hflow x (m - i))))

theorem shape_prod_continuousWithinAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    (m N : ℕ) (x : M) (w : Fin N → TangentSpace I x) :
    ContinuousWithinAt
      (fun t : ℝ => Work.Diff.EXT.Shape (G t) x m
        * ∏ r : Fin N, Real.sqrt ((G t).inner x (w r) (w r)))
      (Set.Ico 0 T) 0 := by
  refine (shape_continuousWithinAt_zero (I := I) (M := M) hflow x m).mul ?_
  refine tendsto_finsetProd Finset.univ (fun r _ => ?_)
  exact (Real.continuous_sqrt.continuousWithinAt).comp
    (inner_continuousWithinAt_zero (I := I) (M := M) hflow x (w r) (w r))
    (fun _ _ => Set.mem_univ _)

end Work.Diff.EXT.evolX
