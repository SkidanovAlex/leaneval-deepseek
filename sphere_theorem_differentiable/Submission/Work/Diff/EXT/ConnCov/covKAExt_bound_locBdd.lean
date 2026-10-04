import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ConnCov.covKAExt_bound_local
import Submission.Work.Diff.EXT.ConnCov.aCovArr_bound_piece

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Time-uniform local boundedness of the `∇^{G 0}`-tower of the connection difference

This file proves `Work.Diff.EXT.ConnCov.covKAExt_bound_locBdd`, the *time-uniform* refinement of the
proved `Work.Diff.EXT.ConnCov.covKAExt_bound_local`: on the compact time interval `[T/2, τ]`
(`τ ∈ Ico (T/2) T`) the constant of the local operator bound may be chosen independently of `s`.

The only time-dependent input of the fixed-time argument `tower_val_bound_nhds` is the compactness
bound of the chart recursion `aCovArr`: at a fixed time that is `aCovArr_compact_bound` (smoothness
of `aCovArr` in the chart coordinate plus compactness).  Uniformly on a *slab* of times it is
`Work.Diff.EXT.ConnCov.aCovArr_bound_piece` (proved, sorry-free): the chart data is jointly smooth on
the open slab `Ioo 0 T ×ˢ target`, and joint smoothness plus compactness of a closed slab gives,
at once, uniform spatial jet bounds for the chart matrix, uniform ellipticity and pointwise
smoothness; `aCovArr_bound_of_jets` then converts the jets into the uniform bound on the recursion
(no Ricci-flow equation, no curvature bound is used there).

Concretely, for `τ ∈ Ico (T/2) T` put `a := (T + τ)/4`.  Then `0 < a`, `2a < T`, and
`Icc (T/2) τ ⊆ Ico a (2a) ∩ Ico (T/2) T`, so on `Icc (T/2) τ` both
* the block `aCovArr G x₀ s k` (`s ∈ Ico a (2a)`, constant `A`) and
* the Gram data (`gram_data_bounds_v2`, uniform on `Ico (T/2) T`, constant `Cl`)
are available with constants independent of `s`.  Re-running the chart estimate
`tower_val_bound_chart` and the finite subcover `CompactSpace.elim_nhds_subcover` gives the result.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **The uniform-in-`s` neighbourhood bound.**  For every point `x` there is a neighbourhood `U` of
`x` and a constant `D ≥ 0` such that on `U`, and *simultaneously for all* `s ∈ Icc (T/2) τ`
(`τ ∈ Ico (T/2) T`), the value of the `∇^{G 0}`-tower of `aOf G s` is bounded by `D` times the
product of the `G s`-norms of its arguments.

This is the uniform version of `tower_val_bound_nhds`: the chart recursion is bounded on the slab
`Ico a (2a)` (`a := (T + τ)/4`) by `aCovArr_bound_piece`, and the Gram data are bounded on
`Ico (T/2) T` by `gram_data_bounds_v2`; `tower_val_bound_chart` then gives the estimate at each
individual `s` with these `s`-independent constants. -/
theorem tower_val_bound_nhds_unif
    [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hG : Submission.Diff.JointSmooth G (Set.Ico 0 T))
    (k : ℕ) {τ : ℝ} (hτ : τ ∈ Set.Ico (T / 2) T) :
    ∀ x : M, ∃ U : Set M, U ∈ 𝓝 x ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ s ∈ Set.Icc (T / 2) τ, ∀ y ∈ U, ∀ (v : Fin k → TangentSpace I y)
        (a b c : TangentSpace I y),
      |Work.Diff.EXT.ATower.valOp
          (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (fun _ => Work.Diff.EXT.aOf G s) k) y v a b c|
        ≤ D * (Finset.univ.prod (fun i : Fin k =>
              Real.sqrt ((G s).inner y (v i) (v i))))
            * Real.sqrt ((G s).inner y a a) * Real.sqrt ((G s).inner y b b)
            * Real.sqrt ((G s).inner y c c) := by
  classical
  intro x₀
  -- the chart coordinate of `x₀`, and a ball around it inside the chart target
  have hsrc : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hmem : (extChartAt I x₀) x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by rwa [extChartAt_source])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hmem)
  set r : ℝ := ε / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hKt : Metric.closedBall ((extChartAt I x₀) x₀) r ⊆ (extChartAt I x₀).target :=
    (Metric.closedBall_subset_ball (by rw [hrdef]; linarith)).trans hball
  have hKc : IsCompact (Metric.closedBall ((extChartAt I x₀) x₀) r) := isCompact_closedBall _ _
  -- the auxiliary time interval `Ico a (2a)`, chosen to contain `[T/2, τ]` inside `[0, T)`
  set a : ℝ := (T + τ) / 4 with hadef
  have ha : 0 < a := by rw [hadef]; linarith [hT, hτ.1]
  have h2a : 2 * a < T := by rw [hadef]; linarith [hτ.2]
  have ha_le : a ≤ T / 2 := by rw [hadef]; linarith [hτ.2]
  have hlt_2a : τ < 2 * a := by rw [hadef]; linarith [hτ.2]
  -- the two uniform constants
  obtain ⟨A, hA0, hAb⟩ :=
    aCovArr_bound_piece (I := I) (M := M) G hT hG x₀
      (Metric.closedBall ((extChartAt I x₀) x₀) r) hKc hKt ha h2a k
  obtain ⟨c, Cl, hc, hCl, _hcCl, hGr⟩ :=
    gram_data_bounds_v2 (I := I) (M := M) G T C hT hC hmet x₀
      (Metric.closedBall ((extChartAt I x₀) x₀) r) hKc hKt
  refine ⟨(extChartAt I x₀) ⁻¹' (Metric.ball ((extChartAt I x₀) x₀) r) ∩ (chartAt H x₀).source,
    Filter.inter_mem ((continuousAt_extChartAt (I := I) x₀).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr)) ((chartAt H x₀).open_source.mem_nhds hsrc),
    A * ((Module.finrank ℝ E : ℝ)
      * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl)) ^ (k+3), ?_, ?_⟩
  · refine mul_nonneg hA0 (pow_nonneg ?_ _)
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCl) (Real.sqrt_nonneg _))
  · intro s hs y hy v a' b' c'
    obtain ⟨hyU, hyS⟩ := hy
    have hyK : (extChartAt I x₀) y ∈ Metric.closedBall ((extChartAt I x₀) x₀) r :=
      Metric.ball_subset_closedBall hyU
    -- `s` lies in the auxiliary slab and in the Gram slab
    have hsA : s ∈ Set.Ico a (2 * a) :=
      ⟨le_trans ha_le hs.1, lt_of_le_of_lt hs.2 hlt_2a⟩
    have hsT : s ∈ Set.Ico (T / 2) T := ⟨hs.1, lt_of_le_of_lt hs.2 hτ.2⟩
    have hpy : Work.Diff.EXT.pt (I := I) x₀ ((extChartAt I x₀) y) = y := by
      refine (extChartAt I x₀).left_inv ?_
      rw [extChartAt_source]
      exact hyS
    have hmain := tower_val_bound_chart (I := I) (M := M) hLC G s k x₀
      (Metric.closedBall ((extChartAt I x₀) x₀) r) hKt hA0 hCl
      (fun u hu => hAb s hsA u hu) (fun u hu i j => (hGr s hsT u hu i j).2)
      ((extChartAt I x₀) y) hyK v a' b' c'
    rwa [hpy] at hmain

/-- **Time-uniform local boundedness of the `∇^{G 0}`-tower of `aOf`.**

The `t`-wise bound is the proved `covKAExt_bound_local`; here the constant must be *uniform* on the
compact time interval `[T/2, τ]` for every `τ ∈ Ico (T/2) T` (it may depend on `τ`, but not on `s`).

ROUTE (the fixed-`t` proof with the constants made uniform in `s`).  In
`Submission/Work/Diff/EXT/ConnCov/covKAExt_bound_local.lean` the chain is
`covKAExt_bound_local` ← `tower_val_bound_nhds` ← `tower_val_bound_chart` ← `aCovArr_compact_bound`
(at the fixed time `t`) + `gram_data_bounds_v2` (already *uniform in `t`*).  Only
`aCovArr_compact_bound` is time-dependent: `aCovArr G x₀ t k v i j l y` must be bounded on the
compact `Icc (T/2) τ × K` (K a closed ball in the chart target) *uniformly in `t`*, which follows
from joint continuity of `(t,y) ↦ aCovArr G x₀ t k v i j l y` there (finitely many `(v,i,j,l)`).

Joint smoothness/continuity of the chart data in `(t,y)`:
* `Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth` (PROVED) and
  `Work.Diff.EXT.contDiffAt_chartMat_of_jointSmooth` give it for the chart matrix of `G t`;
* `Work.Diff.GE.cGam` / `GramM` / `GramInv` are built from it by arithmetic and the *spatial*
  derivative, whose joint smoothness is `Work.Diff.EXT.covK_spatialDeriv` (PROVED) (model space);
* `Work.Diff.EXT.CBound.aCovArr_contDiffAt` is the *fixed-time* smoothness proof of the recursion
  `aCovArr (m+1) = fderiv (aCovArr m) (cBasis ·) − corrFun`; the same induction with the time
  parameter gives joint smoothness, since both terms are joint.
Then re-run `tower_val_bound_nhds` + the finite subcover of `CompactSpace.elim_nhds_subcover`
from `covKAExt_bound_local`, with the uniform `aCovArr` constant instead of the `t`-wise one.

Hypotheses: `hflow : IsRicciFlow G T` supplies `JointSmooth G (Ico 0 T)`, i.e. joint smoothness of
`(s,x) ↦ (G s).inner x` on `Ico 0 T × univ`, so all points of `Icc (T/2) τ × M` are interior points
of joint smoothness (`T/2 > 0`, `τ < T`). -/
theorem covKAExt_bound_locBdd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u) :
    ∀ k : ℕ, ∀ τ ∈ Set.Ico (T / 2) T, ∃ W : ℝ, 0 ≤ W ∧ ∀ s ∈ Set.Icc (T / 2) τ,
      Work.Diff.EXT.ATower.ValBound G s k
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G s) k) W := by
  intro k τ hτ
  have hG : Submission.Diff.JointSmooth G (Set.Ico 0 T) := hflow.1
  have hloc := tower_val_bound_nhds_unif (I := I) (M := M) hLC G T C hT hC hmet hG k hτ
  choose U hU D hD0 hDb using hloc
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  refine ⟨∑ x ∈ s, D x, Finset.sum_nonneg (fun x _ => hD0 x), ?_⟩
  intro t ht y v a b c
  have hy : y ∈ ⋃ x ∈ s, U x := by rw [hs]; trivial
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hxs, hyU⟩ := hy
  refine le_trans (hDb x t ht y hyU v a b c) ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun x _ => hD0 x) hxs) (Finset.prod_nonneg
        (fun i _ => Real.sqrt_nonneg _))) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Work.Diff.EXT.ConnCov
