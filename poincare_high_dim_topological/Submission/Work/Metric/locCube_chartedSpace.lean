/-
Copyright (c) 2024 The poincare_high_dim_topological team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.PL.Defs

/-!
# `LocCube.of_chartedSpace`: a charted space is locally a cube

This file proves `Work.Metric.locCube_chartedSpace`: every charted space over the model cube
`PL.E n = ℝⁿ` satisfies `PL.LocCube n M`, i.e. every point `x` lies in the image of the open
`½`-cube of some *cube chart* (an open embedding of the open unit cube into `M`).

The construction is the obvious one.  Take the preferred chart `e = chartAt (PL.E n) x`, look at
an open ball `ball (e x) ρ ⊆ e.target` inside the chart target, and embed the open unit cube
linearly into that ball by `y ↦ e x + t • y` with `t = ρ / (√n + 1)`.  Since a point of the open
unit cube has Euclidean norm at most `√n`, this scaling lands inside `ball (e x) ρ`, and composing
with `e.symm` gives the required open embedding of the cube into `M`.  The point `0` of the cube
maps to `x`, so `x` lies in the image of the `½`-cube.

This is step C0 of the blueprint (`LocCube.of_chartedSpace`).

## Main results

* `Work.Metric.isOpen_openCube` — the open sup-norm cube of `PL.E n` is open.
* `Work.Metric.norm_le_sqrt_of_mem_openCube_one` — a point of the open unit cube has norm `≤ √n`.
* `Work.Metric.locCube_chartedSpace` — `PL.LocCube n M` for a charted space `M` over `PL.E n`.
-/

open Set Metric
open scoped Topology

namespace Work.Metric

/-- The open sup-norm cube `PL.openCube r ⊆ PL.E n` is open (for every real `r`; it is empty
when `r ≤ 0`). -/
theorem isOpen_openCube (n : ℕ) (r : ℝ) : IsOpen (PL.openCube (n := n) r) := by
  rw [show PL.openCube (n := n) r =
      ⋂ i : Fin n, (fun x : PL.E n => x i) ⁻¹' Set.Ioo (-r) r from ?_]
  · exact isOpen_iInter_of_finite fun i =>
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).isOpen_preimage _ isOpen_Ioo
  · ext x
    simp only [PL.openCube, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage,
      Set.mem_Ioo, abs_lt]

/-- Every point of the open unit cube `PL.openCube 1 ⊆ PL.E n` has Euclidean norm at most
`√n`. -/
theorem norm_le_sqrt_of_mem_openCube_one (n : ℕ) {y : PL.E n}
    (h : y ∈ PL.openCube (n := n) 1) : ‖y‖ ≤ Real.sqrt n := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖y.ofLp i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.norm_eq_abs]
        have hi : |y.ofLp i| < 1 := by
          have := h i
          simpa [PL.openCube] using this
        nlinarith [abs_nonneg (y.ofLp i)]
      _ = n := by simp

/-- **`LocCube` is automatic for a charted space.**  Every charted space over `PL.E n` is locally
a cube: for every point `x` there is a cube chart whose open `½`-cube maps onto a neighbourhood
of `x`. -/
theorem locCube_chartedSpace (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (PL.E n) M] : PL.LocCube n M := by
  intro x
  classical
  set e := chartAt (PL.E n) x
  have hxsrc : x ∈ e.source := mem_chart_source (PL.E n) x
  have hxtgt : e x ∈ e.target := mem_chart_target (PL.E n) x
  -- an open ball inside the chart target around `e x`
  obtain ⟨ρ, hρpos, hρt⟩ := Metric.isOpen_iff.mp e.open_target (e x) hxtgt
  -- the scaling factor, chosen so that the unit cube lands in the ball
  set t : ℝ := ρ / (Real.sqrt n + 1) with ht
  have hden : 0 < Real.sqrt n + 1 := by positivity
  have htpos : 0 < t := div_pos hρpos hden
  have htne : t ≠ 0 := ne_of_gt htpos
  have hmem : ∀ y ∈ PL.openCube (n := n) 1, e x + t • y ∈ e.target := by
    intro y hy
    apply hρt
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : (e x + t • y) - e x = t • y := by abel
    rw [hsub, norm_smul, Real.norm_of_nonneg htpos.le]
    have hyb : ‖y‖ ≤ Real.sqrt n := norm_le_sqrt_of_mem_openCube_one n hy
    have h1 : t * ‖y‖ ≤ t * Real.sqrt n := mul_le_mul_of_nonneg_left hyb htpos.le
    have h2 : t * Real.sqrt n < t * (Real.sqrt n + 1) := by
      apply mul_lt_mul_of_pos_left _ htpos; linarith
    have h3 : t * (Real.sqrt n + 1) = ρ := by
      rw [ht]; field_simp
    linarith
  -- the linear embedding of the whole space `y ↦ e x + t • y` is an open embedding
  have hLemb : Topology.IsOpenEmbedding (fun y : PL.E n => e x + t • y) :=
    (Homeomorph.addLeft (e x)).isOpenEmbedding.comp
      (Homeomorph.smulOfNeZero t htne).isOpenEmbedding
  -- so its restriction to the open cube, viewed in the chart target, is an open embedding
  have hG : Topology.IsOpenEmbedding
      (fun y : (PL.openCube (n := n) 1 : Set (PL.E n)) =>
        (⟨e x + t • y, hmem y y.2⟩ : e.target)) := by
    refine (Topology.IsOpenEmbedding.of_comp_iff _ e.open_target.isOpenEmbedding_subtypeVal).1 ?_
    convert hLemb.comp (isOpen_openCube n 1).isOpenEmbedding_subtypeVal using 1
    ext y; rfl
  -- composing with the inverse chart (an open embedding of the chart target) gives the cube chart
  have hF : Topology.IsOpenEmbedding
      (fun y : (PL.openCube (n := n) 1 : Set (PL.E n)) => e.symm (e x + t • y)) := by
    have hcomp := (e.symm.isOpenEmbedding_restrict).comp hG
    convert hcomp using 1
    ext y; rfl
  refine ⟨⟨fun y : PL.E n => e.symm (e x + t • y), ?_, hF⟩, ?_⟩
  · exact continuousOn_iff_continuous_domRestrict.mpr hF.continuous
  · -- `0` lies in the `½`-cube and is mapped to `x`
    refine ⟨0, ?_, ?_⟩
    · simp [PL.openCube]
    · simp only [smul_zero, add_zero]
      exact e.left_inv hxsrc

end Work.Metric
