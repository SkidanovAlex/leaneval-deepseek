import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Cells.Connell.cubeChart_isCompact_image_closedCube
import Submission.Work.Cells.Connell.cubeChart_isOpen_image_openCube

namespace Work.Cells.Connell

open Set Metric

theorem exists_mesh_of_chart_cover {n : ℕ} {M : Type*} [MetricSpace M]
    (cA cC : PL.CubeChart n M) {α β₀ β : ℝ} (hα : 0 < α) (hαβ₀ : α < β₀) (hβ₀β : β₀ < β)
    (hβ1 : β < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (σ : Set (PL.E n)), σ ⊆ PL.closedCube β →
      (∃ x ∈ σ, cC.toFun x ∈ cA.toFun '' PL.closedCube α) →
      (∀ x ∈ σ, ∀ y ∈ σ, dist x y < δ) → cC.toFun '' σ ⊆ cA.toFun '' PL.openCube β₀ := by
  have hα1 : α < 1 := lt_trans hαβ₀ (lt_trans hβ₀β hβ1)
  have hβ₀1 : β₀ < 1 := lt_trans hβ₀β hβ1
  have hβ₀0 : 0 < β₀ := lt_trans hα hαβ₀
  -- The closed `β`-cube lies in the open unit cube, where `cC` is continuous.
  have hsubβ1 : PL.closedCube (n := n) β ⊆ PL.openCube (n := n) 1 :=
    fun x hx i => lt_of_le_of_lt (hx i) hβ1
  have hUC : UniformContinuousOn cC.toFun (PL.closedCube (n := n) β) :=
    (isCompact_closedCube n β).uniformContinuousOn_of_continuous (cC.cont.mono hsubβ1)
  -- The target open set and the compact set to be engulfed.
  have hUopen : IsOpen (cA.toFun '' PL.openCube (n := n) β₀) :=
    cubeChart_isOpen_image_openCube cA hβ₀0 (le_of_lt hβ₀1)
  have hKcompact : IsCompact (cA.toFun '' PL.closedCube (n := n) α) :=
    cubeChart_isCompact_image_closedCube cA hα1
  have hKsubU : cA.toFun '' PL.closedCube (n := n) α ⊆ cA.toFun '' PL.openCube (n := n) β₀ := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, fun i => lt_of_le_of_lt (hx i) hαβ₀, rfl⟩
  obtain ⟨ε, hε, hthick⟩ := hKcompact.exists_thickening_subset_open hUopen hKsubU
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδ, hUCδ⟩ := hUC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro σ hσ hmeet hdiam
  obtain ⟨x, hxσ, hxK⟩ := hmeet
  rintro w ⟨z, hzσ, rfl⟩
  have hdist : dist (cC.toFun x) (cC.toFun z) < ε :=
    hUCδ x (hσ hxσ) z (hσ hzσ) (hdiam x hxσ z hzσ)
  exact hthick (Metric.mem_thickening_iff.2 ⟨cC.toFun x, hxK, by rw [dist_comm (cC.toFun z) (cC.toFun x)]; exact hdist⟩)

end Work.Cells.Connell
