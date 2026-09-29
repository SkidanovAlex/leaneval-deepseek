import Mathlib
import Submission.Work.TMComp.RealCartanDefs

namespace Work.TMComp.RealCartan

/-- For a closed set `B` with empty interior inside the open ball `ball c R`, the frontier of
the open set `ball c R \ B` is the union of the bounding circle `sphere c R` and `B`. -/
theorem rcFrontier {R : ℝ} (hR : 0 < R) {c : ℂ} {B : Set ℂ} (hB : IsClosed B)
    (hBsub : B ⊆ Metric.ball c R) (hint : interior B = ∅) :
    frontier (Metric.ball c R \ B) = Metric.sphere c R ∪ B := by
  have hRne : R ≠ 0 := ne_of_gt hR
  -- The closure of the full ball.
  have hball_cl : closure (Metric.ball c R) = Metric.closedBall c R := closure_ball c hRne
  -- `B` has empty interior, so its complement is dense.
  have hdense : Dense (Bᶜ) := interior_eq_empty_iff_dense_compl.mp hint
  -- The open ball is contained in the closure of `ball \ B` (`ball` meets the dense `Bᶜ`).
  have hsub : Metric.ball c R ⊆ closure (Metric.ball c R \ B) := by
    have h := hdense.open_subset_closure_inter (Metric.isOpen_ball (x := c) (ε := R))
    simpa only [Set.sdiff_eq] using h
  -- Hence that closure is exactly the closed ball.
  have hclosure : closure (Metric.ball c R \ B) = Metric.closedBall c R := by
    apply le_antisymm
    · rw [← hball_cl]; exact closure_mono Set.sdiff_subset
    · rw [← hball_cl]; exact closure_minimal hsub isClosed_closure
  -- `ball \ B` is open, so its interior is itself.
  have hopen : IsOpen (Metric.ball c R \ B) := Metric.isOpen_ball.sdiff hB
  rw [← closure_sdiff_interior, hclosure, hopen.interior_eq]
  -- `closedBall \ (ball \ B) = (closedBall \ ball) ∪ (closedBall ∩ B)`.
  have h1 : Metric.closedBall c R \ (Metric.ball c R \ B)
      = (Metric.closedBall c R \ Metric.ball c R) ∪ (Metric.closedBall c R ∩ B) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]
    tauto
  rw [h1, Metric.closedBall_sdiff_ball,
    Set.inter_eq_right.mpr (hBsub.trans Metric.ball_subset_closedBall)]

end Work.TMComp.RealCartan
