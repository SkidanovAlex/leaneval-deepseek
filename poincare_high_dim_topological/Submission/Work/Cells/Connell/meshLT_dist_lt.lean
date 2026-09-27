import Mathlib
import Submission.Work.PL.Defs

namespace Work.Cells.Connell

/-- A mesh bound on the vertices of each face bounds the distance between any two points
of the (convex hull of a) face: every point of a simplex is a convex combination of its
vertices, and the diameter of a convex hull is attained at a pair of extreme points
(`convexHull_exists_dist_ge2`). -/
theorem meshLT_dist_lt {N : ℕ} {K : PL.Cx N} {δ : ℝ} (h : PL.MeshLT K δ)
    {s : Finset (PL.E N)} (hs : s ∈ K.faces) {x y : PL.E N} (hx : x ∈ PL.simp s)
    (hy : y ∈ PL.simp s) : dist x y < δ := by
  rw [PL.simp] at hx hy
  obtain ⟨x', hx', y', hy', hle⟩ := convexHull_exists_dist_ge2 hx hy
  rw [PL.MeshLT] at h
  exact lt_of_le_of_lt hle (h s hs x' (Finset.mem_coe.mp hx') y' (Finset.mem_coe.mp hy'))

end Work.Cells.Connell
