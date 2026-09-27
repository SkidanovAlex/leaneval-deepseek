import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Finite

open Set Metric
open scoped BigOperators

/-- The diameter of the convex hull of a finite vertex set is at most any bound on the pairwise
distances of its vertices. -/
lemma dist_le_of_mem_convexHull_finset {n : ℕ} (s : Finset (PL.E n)) {d : ℝ}
    (hd : ∀ v ∈ s, ∀ w ∈ s, dist v w ≤ d) :
    ∀ x ∈ convexHull ℝ (s : Set (PL.E n)), ∀ y ∈ convexHull ℝ (s : Set (PL.E n)), dist x y ≤ d := by
  intro x hx y hy
  have h1 : ∀ v ∈ s, dist x v ≤ d := by
    intro v hv
    have hsub : (s : Set (PL.E n)) ⊆ Metric.closedBall v d := by
      intro w hw
      simpa [Metric.mem_closedBall, dist_comm] using hd w hw v hv
    exact convexHull_min hsub (convex_closedBall v d) hx
  have hsub2 : (s : Set (PL.E n)) ⊆ Metric.closedBall x d := by
    intro w hw
    simpa [Metric.mem_closedBall, dist_comm] using h1 w hw
  have hmem := convexHull_min hsub2 (convex_closedBall x d) hy
  simpa [Metric.mem_closedBall, dist_comm] using hmem

/-- Points of a simplex of a complex with mesh `< δ` are pairwise at distance `< δ`. -/
lemma dist_lt_of_mesh {N : ℕ} (K : PL.Cx N) {δ : ℝ} (h : PL.MeshLT K δ) {s : Finset (PL.E N)}
    (hs : s ∈ K.faces) {x y : PL.E N} (hx : x ∈ PL.simp s) (hy : y ∈ PL.simp s) : dist x y < δ := by
  have hsne : s.Nonempty := K.nonempty_of_mem_faces hs
  set d := s.sup' hsne (fun v => s.sup' hsne (fun w => dist v w)) with hddef
  have hd_lt : d < δ := by
    rw [hddef, Finset.sup'_lt_iff]
    intro v hv
    rw [Finset.sup'_lt_iff]
    intro w hw
    exact h s hs v hv w hw
  have hd_le : ∀ v ∈ s, ∀ w ∈ s, dist v w ≤ d := by
    intro v hv w hw
    rw [hddef]
    calc dist v w ≤ s.sup' hsne (fun w => dist v w) := Finset.le_sup' (fun w => dist v w) hw
      _ ≤ s.sup' hsne (fun v => s.sup' hsne (fun w => dist v w)) :=
            Finset.le_sup' (fun v => s.sup' hsne (fun w => dist v w)) hv
  have := dist_le_of_mem_convexHull_finset s hd_le x hx y hy
  linarith

end Work.PL.Approx.Finite
