import Mathlib
import Submission.Work.WilE8.Star.LiftDefs

namespace Work.WilE8.Star

/-- The cylinder over a `W ⊆ ℝ^{n+m}` in the coordinates `1, …, n+m` (i.e. the set of
`x ∈ ℝ^{(n+1)+m}` with `tailM n m x ∈ W`), cut by the cube, projects onto the cube of
`ℝ^{n+1}` intersected with the cylinder over `projFirst n m '' W`.

In other words, dropping the *first* coordinate of a point of the cube over `W` and
projecting to the first `n+1` coordinates is the same as intersecting the cube with the
cylinder (over the `Fin.tail`-coordinates) on the image of `W`. -/
theorem projFirst_cylinder {n m : ℕ} {W : Set (Fin (n + m) → ℝ)}
    (hW : W ⊆ WilkiesDesign.E.cubeC (n + m)) :
    WilkiesDesign.E.projFirst (n + 1) m ''
        ({x : Fin ((n + 1) + m) → ℝ | Work.WilE8.Star.tailM n m x ∈ W} ∩
          WilkiesDesign.E.cubeC ((n + 1) + m))
      = {z : Fin (n + 1) → ℝ |
          z ∈ WilkiesDesign.E.cubeC (n + 1) ∧
          Fin.tail z ∈ WilkiesDesign.E.projFirst n m '' W} := by
  ext z
  constructor
  · rintro ⟨x, ⟨hxW, hxcube⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← Work.WilE8.projFirst_image_cubeC (n + 1) m]
      exact ⟨x, hxcube, rfl⟩
    · rw [tail_projFirst]
      exact ⟨tailM n m x, hxW, rfl⟩
  · rintro ⟨hzcube, y, hyW, hy⟩
    refine ⟨consV n m (z 0) y, ⟨?_, ?_⟩, ?_⟩
    · simpa using hyW
    · rw [consV_mem_cubeC]
      exact ⟨abs_le.mp (hzcube 0), hW hyW⟩
    · rw [projFirst_consV, hy, Fin.cons_self_tail]

end Work.WilE8.Star
