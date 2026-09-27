import Mathlib
import Submission.Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace

namespace Work.Generic

/-- Finset version of the "finitely many proper affine subspaces miss a point of every ball"
lemma: it is the `iUnion` statement of `Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace`
applied to the subtype `{F // F ∈ G}` of the finite set `G`. -/
theorem exists_mem_ball_notMem_finset {m : ℕ} (G : Finset (AffineSubspace ℝ (PL.E m)))
    (hG : ∀ F ∈ G, F ≠ ⊤) (x : PL.E m) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ Metric.ball x ε, ∀ F ∈ G, y ∉ (F : Set (PL.E m)) := by
  obtain ⟨y, hy, h⟩ :=
    Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace (ι := {F // F ∈ G})
      (fun i => (i : AffineSubspace ℝ (PL.E m))) (fun i => hG i.1 i.2) x hε
  exact ⟨y, hy, fun F hF => h ⟨F, hF⟩⟩

end Work.Generic
