/-
Copyright (c) 2024 The poincare_high_dim_topological team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.Metric.Basic

/-!
# Finite chart ball covers

A compact charted space `M` over a (pseudo)metric model space `E` admits a finite cover by chart
balls whose closed balls are contained in the corresponding chart targets
(`Work.Metric.exists_chartBallCover`), and every compact subset of `M` is covered by finitely many
members of any given chart ball cover (`Work.Metric.ChartBallCover.exists_finite_subcover_of_isCompact`).

When `M` carries a compatible metric we also prove:

* `Work.Metric.exists_chartBallCover_diam_le`: for every `ε > 0` there is a chart ball cover all of
  whose members have diameter `≤ ε`;
* `Work.Metric.ChartBallCover.exists_pos_diam_lt_subset`: the Lebesgue number lemma for a chart ball
  cover -- every nonempty set of diameter `< δ` (for some `δ > 0`) lies in one chart ball of the
  cover;
* `Work.Metric.exists_chartBallCover_diam_lebesgue`: the two combined.
-/

open Set Metric
open scoped Topology

namespace Work.Metric

variable {E : Type*} [PseudoMetricSpace E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A compact charted space admits a finite cover by chart balls whose closed balls are contained
in the corresponding chart targets. -/
theorem exists_chartBallCover [CompactSpace M] : Nonempty (ChartBallCover E M) := by
  have key : ∀ x : M, ∃ r : ℝ, 0 < r ∧ closedBall (chartAt E x x) r ⊆ (chartAt E x).target := by
    intro x
    obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.mp (chart_target_mem_nhds E x)
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεt⟩
  choose r hrpos hrsub using key
  have hcover : (⋃ x : M, chartBall (E := E) x (r x)) = univ := by
    rw [eq_univ_iff_forall]
    exact fun x => mem_iUnion.mpr ⟨x, mem_chartBall_self (hrpos x)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => chartBall (E := E) x (r x))
    (fun x => isOpen_chartBall (ball_subset_target_of_closedBall_subset_target (hrsub x)))
    (by rw [hcover])
  haveI : Fintype {x : M // x ∈ t} := inferInstance
  refine ⟨{
    ι := {x : M // x ∈ t}
    center := fun i => (i : M)
    radius := fun i => r (i : M)
    radius_pos := fun i => hrpos (i : M)
    closedBall_subset_target := fun i => hrsub (i : M)
    cover := ?_ }⟩
  rw [Set.iUnion_subtype]
  exact eq_univ_iff_forall.mpr fun x => ht (mem_univ x)

namespace ChartBallCover

variable (C : ChartBallCover E M)

/-- A compact subset of `M` is covered by finitely many members of a chart ball cover. -/
theorem exists_finite_subcover_of_isCompact {K : Set M} (hK : IsCompact K) :
    ∃ t : Finset C.ι, K ⊆ ⋃ i ∈ t, chartBall (E := E) (C.center i) (C.radius i) :=
  hK.elim_finite_subcover _ (fun i => C.isOpen i) (by rw [C.cover]; exact subset_univ K)

/-- The closed chart balls of a chart ball cover also cover `M`. -/
theorem iUnion_chartClosedBall :
    (⋃ i, chartClosedBall (E := E) (C.center i) (C.radius i)) = univ := by
  have h := iUnion_mono (fun i =>
    chartBall_subset_chartClosedBall (E := E) (C.center i) (C.radius i))
  rw [C.cover] at h
  exact top_le_iff.mp h

/-- Every point of `M` lies in one of the chart balls of the cover. -/
theorem exists_mem (x : M) : ∃ i, x ∈ chartBall (E := E) (C.center i) (C.radius i) :=
  C.exists_chartBall_of_mem x

end ChartBallCover

section Metric

variable {M' : Type*} [MetricSpace M'] [ChartedSpace E M']

/-- For every `ε > 0`, a compact charted metric space admits a finite chart ball cover all of whose
members have diameter at most `ε`. -/
theorem exists_chartBallCover_diam_le [CompactSpace M'] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ChartBallCover E M',
      ∀ i, Metric.diam (chartBall (E := E) (C.center i) (C.radius i)) ≤ ε := by
  have key : ∀ x : M', ∃ r : ℝ, 0 < r ∧
      closedBall (chartAt E x x) r ⊆ (chartAt E x).target ∧
      chartBall (E := E) x r ⊆ closedBall x (ε / 2) := by
    intro x
    have hmem : closedBall x (ε / 2) ∈ 𝓝 x :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self (half_pos hε)))
        ball_subset_closedBall
    obtain ⟨r₁, hr₁, hr₁t, hr₁V⟩ := exists_chartBall_subset_of_mem_nhds (E := E) hmem
    refine ⟨r₁ / 2, half_pos hr₁, ?_, ?_⟩
    · exact (closedBall_subset_ball (half_lt_self hr₁)).trans
        (ball_subset_target_of_closedBall_subset_target hr₁t)
    · exact (chartBall_mono (half_le_self hr₁.le)).trans hr₁V
  choose r hrpos hrsub hrball using key
  have hcover : (⋃ x : M', chartBall (E := E) x (r x)) = univ := by
    rw [eq_univ_iff_forall]
    exact fun x => mem_iUnion.mpr ⟨x, mem_chartBall_self (hrpos x)⟩
  have hdiam : ∀ x : M', Metric.diam (chartBall (E := E) x (r x)) ≤ ε := by
    intro x
    have h2 : (2 : ℝ) * (ε / 2) = ε := by ring
    have h := Metric.diam_le_of_subset_closedBall (le_of_lt (half_pos hε)) (hrball x)
    rwa [h2] at h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M' => chartBall (E := E) x (r x))
    (fun x => isOpen_chartBall (ball_subset_target_of_closedBall_subset_target (hrsub x)))
    (by rw [hcover])
  haveI : Fintype {x : M' // x ∈ t} := inferInstance
  refine ⟨{
    ι := {x : M' // x ∈ t}
    center := fun i => (i : M')
    radius := fun i => r (i : M')
    radius_pos := fun i => hrpos (i : M')
    closedBall_subset_target := fun i => hrsub (i : M')
    cover := ?_ }, ?_⟩
  · rw [Set.iUnion_subtype]
    exact eq_univ_iff_forall.mpr fun x => ht (mem_univ x)
  · intro i
    exact hdiam (i : M')

namespace ChartBallCover

variable (C : ChartBallCover E M')

/-- **Lebesgue number lemma for a chart ball cover.**  In a compact charted metric space, for any
chart ball cover there is `δ > 0` such that every nonempty set of diameter `< δ` is contained in
one of the chart balls of the cover. -/
theorem exists_pos_diam_lt_subset [CompactSpace M'] :
    ∃ δ > 0, ∀ S : Set M', S.Nonempty → Metric.diam S < δ →
      ∃ i, S ⊆ chartBall (E := E) (C.center i) (C.radius i) := by
  obtain ⟨δ, hδ, h⟩ := CompactSpace.lebesgue_number_lemma
    (fun i : C.ι => chartBall (E := E) (C.center i) (C.radius i)) (fun i => C.isOpen i)
    (by rw [C.cover])
  exact ⟨δ, hδ, fun S hS hd => h S hS hd.le⟩

end ChartBallCover

/-- For every `ε > 0`, a compact charted metric space admits a chart ball cover whose members all
have diameter `≤ ε`, together with a Lebesgue number for it. -/
theorem exists_chartBallCover_diam_lebesgue [CompactSpace M'] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ChartBallCover E M',
      (∀ i, Metric.diam (chartBall (E := E) (C.center i) (C.radius i)) ≤ ε) ∧
      (∃ δ > 0, ∀ S : Set M', S.Nonempty → Metric.diam S < δ →
        ∃ i, S ⊆ chartBall (E := E) (C.center i) (C.radius i)) := by
  obtain ⟨C, hC⟩ := exists_chartBallCover_diam_le (E := E) (M' := M') hε
  exact ⟨C, hC, C.exists_pos_diam_lt_subset⟩

end Metric

end Work.Metric
