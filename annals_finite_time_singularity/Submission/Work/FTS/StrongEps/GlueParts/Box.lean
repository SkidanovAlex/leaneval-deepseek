/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/GlueParts/Box.lean` — boxes in `ℝ × ℝ × ℝ` and unique differentiability of closed intervals
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.StrongEps.GlueParts.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 concat uncurry3)

/-! ## Boxes, and unique differentiability of the closed fake-time intervals -/

/-- The open box of radius `α` around `p` (same radius in the three coordinates). -/
def box3 (p : P3) (α : ℝ) : Set P3 :=
  Set.Ioo (p.1 - α) (p.1 + α) ×ˢ Set.Ioo (p.2.1 - α) (p.2.1 + α) ×ˢ
    Set.Ioo (p.2.2 - α) (p.2.2 + α)

theorem isOpen_box3 (p : P3) (α : ℝ) : IsOpen (box3 p α) :=
  isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)

theorem mem_box3_self {p : P3} {α : ℝ} (hα : 0 < α) : p ∈ box3 p α := by
  simp only [box3, Set.mem_prod, Set.mem_Ioo]
  exact ⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩⟩⟩

theorem box3_subset_ball {p : P3} {α : ℝ} (hα : 0 < α) : box3 p α ⊆ Metric.ball p α := by
  intro q hq
  obtain ⟨h1, h2, h3⟩ := hq
  rw [Set.mem_Ioo] at h1 h2 h3
  rw [Metric.mem_ball, Prod.dist_eq]
  refine max_lt ?_ ?_
  · rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  · rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    · rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [h3.1], by linarith [h3.2]⟩

theorem exists_box3_subset_of_mem_nhds {p : P3} {V : Set P3} (hV : V ∈ 𝓝 p) :
    ∃ α : ℝ, 0 < α ∧ box3 p α ⊆ V := by
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  exact ⟨ε / 2, by linarith, fun q hq =>
    hεV (Metric.ball_subset_ball (by linarith) (box3_subset_ball (by linarith) hq))⟩

/-- The closed interval `Icc a b` (`a < b`) is a set of unique differentiability at each of its
points. -/
theorem uniqueDiffWithinAt_Icc {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) :
    UniqueDiffWithinAt ℝ (Set.Icc a b) x :=
  uniqueDiffWithinAt_convex (convex_Icc a b) ⟨(a + b) / 2, by
    rw [interior_Icc]; exact ⟨by linarith, by linarith⟩⟩ (subset_closure hx)

theorem mem_box3_iff {p q : P3} {α : ℝ} :
    q ∈ box3 p α ↔ (p.1 - α < q.1 ∧ q.1 < p.1 + α) ∧ (p.2.1 - α < q.2.1 ∧ q.2.1 < p.2.1 + α)
      ∧ (p.2.2 - α < q.2.2 ∧ q.2.2 < p.2.2 + α) := by
  simp only [box3, Set.mem_prod, Set.mem_Ioo]

theorem box3_mono {p : P3} {α β : ℝ} (h : α ≤ β) : box3 p α ⊆ box3 p β := by
  intro q hq
  rw [mem_box3_iff] at hq ⊢
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hq
  exact ⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩⟩⟩


end Work.FTS.StrongEps.GlueParts
