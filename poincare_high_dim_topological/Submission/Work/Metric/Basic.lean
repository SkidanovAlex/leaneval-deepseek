/-
Copyright (c) 2024 The poincare_high_dim_topological team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Chart balls in a charted space

Let `E` be a (pseudo)metric space and `M` a charted space over `E` (a topological space with an
atlas of partial homeomorphisms onto open subsets of `E`).  For `x : M` and `r : ℝ`, the
*open chart ball* `chartBall x r` is the image, under the inverse of the preferred chart at `x`,
of the open ball of radius `r` around `chartAt E x x` in the model space `E`; the *closed chart
ball* `chartClosedBall x r` is defined analogously.

These are the basic building blocks for the "finite atlas of chart balls" used in the
Stallings–Zeeman–Newman engulfing proof of the high-dimensional Poincaré conjecture: every
chart ball is an open cell, its closed version is compact when `E` is proper, and the chart balls
at a point form a neighbourhood basis.

## Main definitions

* `Work.Metric.chartBall`, `Work.Metric.chartClosedBall`
* `Work.Metric.ChartBallCover`: a finite cover of `M` by chart balls whose closed balls are
  contained in the corresponding chart targets ("closed-ball shrinkings").

## Main results

* `Work.Metric.isOpen_chartBall`, `Work.Metric.chartBall_eq_inter_preimage`
* `Work.Metric.exists_chartBall_subset_of_mem_nhds`: chart balls form a neighbourhood basis.
* `Work.Metric.ChartBallCover.exists_chartBall_of_mem` : the chart balls of a `ChartBallCover`
  cover `M`.
-/

open Set Metric
open scoped Topology

namespace Work.Metric

universe u v

variable {E : Type u} [PseudoMetricSpace E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]

/-- `chartBall x r` is the open ball of radius `r` around `x`, seen in the chart at `x`: the image
of `ball (chartAt E x x) r` under the inverse of the chart at `x`. -/
def chartBall (x : M) (r : ℝ) : Set M := (chartAt E x).symm '' ball (chartAt E x x) r

/-- `chartClosedBall x r` is the closed ball of radius `r` around `x`, seen in the chart at `x`. -/
def chartClosedBall (x : M) (r : ℝ) : Set M := (chartAt E x).symm '' closedBall (chartAt E x x) r

theorem chartBall_def (x : M) (r : ℝ) :
    chartBall (E := E) x r = (chartAt E x).symm '' ball (chartAt E x x) r := rfl

theorem chartClosedBall_def (x : M) (r : ℝ) :
    chartClosedBall (E := E) x r = (chartAt E x).symm '' closedBall (chartAt E x x) r := rfl

/-- If the ball of radius `r` around `chartAt E x x` lies in the chart target, then the chart ball
is the trace of the chart on that ball. -/
theorem chartBall_eq_inter_preimage {x : M} {r : ℝ}
    (h : ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartBall (E := E) x r = (chartAt E x).source ∩ (chartAt E x) ⁻¹' ball (chartAt E x x) r :=
  (chartAt E x).symm_image_eq_source_inter_preimage h

theorem chartClosedBall_eq_inter_preimage {x : M} {r : ℝ}
    (h : closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartClosedBall (E := E) x r =
      (chartAt E x).source ∩ (chartAt E x) ⁻¹' closedBall (chartAt E x x) r :=
  (chartAt E x).symm_image_eq_source_inter_preimage h

theorem ball_subset_target_of_closedBall_subset_target {x : M} {r : ℝ}
    (h : closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    ball (chartAt E x x) r ⊆ (chartAt E x).target :=
  ball_subset_closedBall.trans h

theorem chartBall_subset_source {x : M} {r : ℝ}
    (h : ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartBall (E := E) x r ⊆ (chartAt E x).source := by
  rw [chartBall_eq_inter_preimage h]
  exact inter_subset_left

theorem mem_chartBall_iff {x : M} {r : ℝ} (h : ball (chartAt E x x) r ⊆ (chartAt E x).target)
    {y : M} :
    y ∈ chartBall (E := E) x r ↔ y ∈ (chartAt E x).source ∧
      chartAt E x y ∈ ball (chartAt E x x) r := by
  rw [chartBall_eq_inter_preimage h, mem_inter_iff, mem_preimage]

theorem isOpen_chartBall {x : M} {r : ℝ} (h : ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    IsOpen (chartBall (E := E) x r) :=
  (chartAt E x).isOpen_image_symm_of_subset_target isOpen_ball h

theorem mem_chartBall_self {x : M} {r : ℝ} (hr : 0 < r) : x ∈ chartBall (E := E) x r := by
  rw [chartBall_def]
  exact ⟨chartAt E x x, mem_ball_self hr,
    PartialHomeomorph.left_inv _ (mem_chart_source E x)⟩

theorem chartBall_mono {x : M} {r r' : ℝ} (h : r ≤ r') :
    chartBall (E := E) x r ⊆ chartBall (E := E) x r' :=
  image_mono (ball_subset_ball h)

theorem chartClosedBall_mono {x : M} {r r' : ℝ} (h : r ≤ r') :
    chartClosedBall (E := E) x r ⊆ chartClosedBall (E := E) x r' :=
  image_mono (closedBall_subset_closedBall h)

theorem chartBall_subset_chartClosedBall (x : M) (r : ℝ) :
    chartBall (E := E) x r ⊆ chartClosedBall (E := E) x r :=
  image_mono ball_subset_closedBall

theorem chartClosedBall_subset_chartBall {x : M} {r r' : ℝ} (h : r < r') :
    chartClosedBall (E := E) x r ⊆ chartBall (E := E) x r' :=
  image_mono (closedBall_subset_ball h)

theorem image_chartBall {x : M} {r : ℝ} (h : ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    (chartAt E x) '' chartBall (E := E) x r = ball (chartAt E x x) r :=
  (chartAt E x).image_symm_image_of_subset_target h

theorem image_chartClosedBall {x : M} {r : ℝ}
    (h : closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    (chartAt E x) '' chartClosedBall (E := E) x r = closedBall (chartAt E x x) r :=
  (chartAt E x).image_symm_image_of_subset_target h

theorem mem_chartClosedBall_iff {x : M} {r : ℝ}
    (h : closedBall (chartAt E x x) r ⊆ (chartAt E x).target) {y : M} :
    y ∈ chartClosedBall (E := E) x r ↔ y ∈ (chartAt E x).source ∧
      chartAt E x y ∈ closedBall (chartAt E x x) r := by
  rw [chartClosedBall_eq_inter_preimage h, mem_inter_iff, mem_preimage]

/-- The restriction of the chart at `x` is a homeomorphism from the chart ball of radius `r` onto
the ball of radius `r` in the model space. -/
noncomputable def chartBallHomeomorph {x : M} {r : ℝ}
    (h : ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartBall (E := E) x r ≃ₜ ball (chartAt E x x) r :=
  (chartAt E x).homeomorphOfImageSubsetSource (s := chartBall (E := E) x r)
    (t := ball (chartAt E x x) r) (chartBall_subset_source h) (image_chartBall h)

/-- The restriction of the chart at `x` is a homeomorphism from the closed chart ball of radius
`r` onto the closed ball of radius `r` in the model space. -/
noncomputable def chartClosedBallHomeomorph {x : M} {r : ℝ}
    (h : closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartClosedBall (E := E) x r ≃ₜ closedBall (chartAt E x x) r :=
  (chartAt E x).homeomorphOfImageSubsetSource (s := chartClosedBall (E := E) x r)
    (t := closedBall (chartAt E x x) r)
    (chartClosedBall_eq_inter_preimage h ▸ inter_subset_left) (image_chartClosedBall h)

/-- A closed chart ball is closed in `M`, when `E` is proper. -/
theorem isCompact_chartClosedBall [ProperSpace E] {x : M} {r : ℝ}
    (h : closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    IsCompact (chartClosedBall (E := E) x r) :=
  (isCompact_closedBall _ _).image_of_continuousOn ((chartAt E x).continuousOn_symm.mono h)

theorem isClosed_chartClosedBall [ProperSpace E] [T2Space M] {x : M} {r : ℝ}
    (h : closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    IsClosed (chartClosedBall (E := E) x r) :=
  (isCompact_chartClosedBall h).isClosed

/-- The closure of a chart ball is contained in the closed chart ball, when `E` is proper. -/
theorem closure_chartBall_subset_chartClosedBall [ProperSpace E] [T2Space M] {x : M} {r : ℝ}
    (h : closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    closure (chartBall (E := E) x r) ⊆ chartClosedBall (E := E) x r :=
  closure_minimal (chartBall_subset_chartClosedBall x r) (isClosed_chartClosedBall h)

/-- For every neighbourhood `V` of `x` there is a chart ball at `x` with closed ball contained
in the chart target and contained in `V`. -/
theorem exists_chartBall_subset_of_mem_nhds {x : M} {V : Set M} (hV : V ∈ 𝓝 x) :
    ∃ r > 0, closedBall (chartAt E x x) r ⊆ (chartAt E x).target ∧
      chartBall (E := E) x r ⊆ V := by
  have hne : (chartAt E x).symm (chartAt E x x) = x :=
    PartialHomeomorph.left_inv _ (mem_chart_source E x)
  have h1 : (chartAt E x).symm ⁻¹' V ∈ 𝓝 (chartAt E x x) :=
    ((chartAt E x).continuousAt_symm (mem_chart_target E x)).preimage_mem_nhds (by rw [hne]; exact hV)
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.mem_nhds_iff.mp h1
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.mem_nhds_iff.mp (chart_target_mem_nhds E x)
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  refine ⟨min r₁ r₂ / 2, half_pos hr, ?_, ?_⟩
  · exact (closedBall_subset_ball (half_lt_self hr)).trans
      ((ball_subset_ball (min_le_right r₁ r₂)).trans h₂)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact h₁ (ball_subset_ball (min_le_left r₁ r₂) (ball_subset_ball (half_le_self hr.le) hz))

/-- Chart balls form a neighbourhood basis at their centre. -/
theorem nhds_hasBasis_chartBall (x : M) :
    (𝓝 x).HasBasis (fun r : ℝ => 0 < r ∧ closedBall (chartAt E x x) r ⊆ (chartAt E x).target)
      (fun r => chartBall (E := E) x r) := by
  refine Filter.HasBasis.mk (fun V => ⟨fun hV => ?_, ?_⟩)
  · obtain ⟨r, hr, hrt, hrV⟩ := exists_chartBall_subset_of_mem_nhds (E := E) hV
    exact ⟨r, ⟨hr, hrt⟩, hrV⟩
  · rintro ⟨r, ⟨hr, hrt⟩, hrV⟩
    refine Filter.mem_of_superset ?_ hrV
    rw [chartBall_eq_inter_preimage (ball_subset_target_of_closedBall_subset_target hrt)]
    exact Filter.inter_mem (chart_source_mem_nhds E x)
      (((chartAt E x).continuousAt (mem_chart_source E x)).preimage_mem_nhds
        (isOpen_ball.mem_nhds (mem_ball_self hr)))

theorem chartBall_eq_empty_iff (x : M) (r : ℝ) : chartBall (E := E) x r = ∅ ↔ r ≤ 0 := by
  rw [chartBall_def, image_eq_empty, Metric.ball_eq_empty]

theorem chartClosedBall_eq_empty_iff (x : M) (r : ℝ) :
    chartClosedBall (E := E) x r = ∅ ↔ r < 0 := by
  rw [chartClosedBall_def, image_eq_empty, Metric.closedBall_eq_empty]

/-- A finite cover of `M` by chart balls whose closed balls of the same radius are contained in
the corresponding chart targets.  This is the "finite atlas of chart balls with closed-ball
shrinkings" used by the engulfing argument. -/
structure ChartBallCover (E : Type u) (M : Type v) [PseudoMetricSpace E] [TopologicalSpace M]
    [ChartedSpace E M] where
  /-- The (finite) index type of the cover. -/
  ι : Type v
  [fintype : Fintype ι]
  /-- The centre of each chart ball. -/
  center : ι → M
  /-- The radius of each chart ball. -/
  radius : ι → ℝ
  /-- Radii are positive. -/
  radius_pos : ∀ i, 0 < radius i
  /-- The closed ball of the same radius is contained in the chart target. -/
  closedBall_subset_target : ∀ i,
    closedBall (chartAt E (center i) (center i)) (radius i) ⊆ (chartAt E (center i)).target
  /-- The chart balls cover `M`. -/
  cover : ⋃ i, chartBall (E := E) (center i) (radius i) = univ

attribute [instance] ChartBallCover.fintype

namespace ChartBallCover

variable (C : ChartBallCover E M)

theorem ball_subset_target (i : C.ι) :
    ball (chartAt E (C.center i) (C.center i)) (C.radius i) ⊆
      (chartAt E (C.center i)).target :=
  ball_subset_target_of_closedBall_subset_target (C.closedBall_subset_target i)

theorem isOpen (i : C.ι) : IsOpen (chartBall (E := E) (C.center i) (C.radius i)) :=
  isOpen_chartBall (C.ball_subset_target i)

theorem subset_source (i : C.ι) :
    chartBall (E := E) (C.center i) (C.radius i) ⊆ (chartAt E (C.center i)).source :=
  chartBall_subset_source (C.ball_subset_target i)

/-- Every closed chart ball of a chart ball cover is compact, when the model space is proper. -/
theorem isCompact_chartClosedBall [ProperSpace E] [T2Space M] (i : C.ι) :
    IsCompact (chartClosedBall (E := E) (C.center i) (C.radius i)) :=
  Work.Metric.isCompact_chartClosedBall (C.closedBall_subset_target i)

/-- Every closed chart ball of a chart ball cover is closed, when the model space is proper. -/
theorem isClosed_chartClosedBall [ProperSpace E] [T2Space M] (i : C.ι) :
    IsClosed (chartClosedBall (E := E) (C.center i) (C.radius i)) :=
  Work.Metric.isClosed_chartClosedBall (C.closedBall_subset_target i)

/-- The closure of a member of a chart ball cover is compact, when the model space is proper. -/
theorem isCompact_closure_chartBall [ProperSpace E] [T2Space M] (i : C.ι) :
    IsCompact (closure (chartBall (E := E) (C.center i) (C.radius i))) :=
  (C.isCompact_chartClosedBall i).of_isClosed_subset isClosed_closure
    (closure_chartBall_subset_chartClosedBall (C.closedBall_subset_target i))

/-- Every point of `M` lies in one of the chart balls of a chart ball cover. -/
theorem exists_chartBall_of_mem (x : M) : ∃ i, x ∈ chartBall (E := E) (C.center i) (C.radius i) :=
  mem_iUnion.mp (by rw [C.cover]; exact trivial)

theorem iUnion_chartBall : ⋃ i, chartBall (E := E) (C.center i) (C.radius i) = univ := C.cover

/-- The chart balls of a chart ball cover form an open cover of `M`. -/
theorem isOpenCover : ∀ i, IsOpen (chartBall (E := E) (C.center i) (C.radius i)) := C.isOpen

end ChartBallCover

end Work.Metric
