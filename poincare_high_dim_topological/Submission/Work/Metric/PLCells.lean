/-
Copyright (c) 2024 The poincare_high_dim_topological team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.PL.Defs
import Submission.Work.Metric.Cell
import Submission.Work.Metric.Euclidean

/-!
# C3 of the blueprint: a compact charted space is a finite union of open cells

This file delivers the `Metric` area's part of the lead's blueprint (C3):
`Work.Metric.cellCover_exists` — a compact charted space over `PL.E n` admits a `PL.CellCover`
(finitely many open `n`-cells covering it), together with the padding step
`Work.Metric.cellCover_succ` and the bridge between the chart balls of this area and the frozen
`PL.IsOpenCell` predicate.
-/

open Set Metric TopologicalSpace Filter

namespace Work.Metric

/-- Every chart ball (with positive radius and closed ball inside the chart target) of a charted
space over `PL.E n` is an open `n`-cell in the sense of the frozen `PL` vocabulary. -/
theorem isOpenCell_chartBall {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (PL.E n) M] {x : M} {r : ℝ} (hr : 0 < r)
    (h : Metric.ball (chartAt (PL.E n) x x) r ⊆ (chartAt (PL.E n) x).target) :
    PL.IsOpenCell n (chartBall (E := PL.E n) x r) :=
  ⟨isOpen_chartBall h, nonempty_chartBall_homeomorph_space hr h⟩

/-- Every member of a `ChartBallCover` of a charted space over `PL.E n` is an open `n`-cell. -/
theorem ChartBallCover.isOpenCell {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (PL.E n) M] (C : ChartBallCover (PL.E n) M) (i : C.ι) :
    PL.IsOpenCell n (chartBall (E := PL.E n) (C.center i) (C.radius i)) :=
  isOpenCell_chartBall (C.radius_pos i)
    (ball_subset_target_of_closedBall_subset_target (C.closedBall_subset_target i))

/-- **Blueprint C3.**  A compact charted space over `PL.E n` is a union of finitely many open
`n`-cells. -/
theorem cellCover_exists (n : ℕ) (M : Type*) [TopologicalSpace M] [ChartedSpace (PL.E n) M]
    [CompactSpace M] : ∃ k, PL.CellCover n M k := by
  classical
  obtain ⟨C⟩ := exists_chartBallCover (E := PL.E n) (M := M)
  let e : C.ι ≃ Fin (Fintype.card C.ι) := Fintype.equivFin C.ι
  refine ⟨Fintype.card C.ι, fun i => chartBall (E := PL.E n) (C.center (e.symm i))
    (C.radius (e.symm i)), ?_, ?_⟩
  · intro i
    exact isOpenCell_chartBall (C.radius_pos _)
      (ball_subset_target_of_closedBall_subset_target (C.closedBall_subset_target _))
  · rw [← C.cover]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, hi⟩
    · rintro ⟨j, hj⟩
      exact ⟨e j, by simpa using hj⟩

/-- A `CellCover` with at least one cell can be padded by one more cell (duplicating the first). -/
theorem cellCover_succ {n k : ℕ} {M : Type*} [TopologicalSpace M] (hk : 1 ≤ k)
    (h : PL.CellCover n M k) : PL.CellCover n M (k + 1) := by
  obtain ⟨W, hW, hcov⟩ := h
  refine ⟨Fin.cases (W ⟨0, hk⟩) W, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simpa using hW ⟨0, hk⟩
    | succ j => simpa using hW j
  · rw [← hcov]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      induction i using Fin.cases with
      | zero => exact ⟨⟨0, hk⟩, by simpa using hi⟩
      | succ j => exact ⟨j, by simpa using hi⟩
    · rintro ⟨j, hj⟩
      exact ⟨Fin.succ j, by simpa using hj⟩

end Work.Metric
