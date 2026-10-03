import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORVonNeumann.Rep.delta1_separating

namespace Work.ORP311

/-- **`matOp` is faithful**: a matrix over `N(G)` acts on the finite direct sum `⊕ ℓ²(G)`
as the operator with coordinates `(matOp A x)_i = ∑_j A_{ij} (x_j)`
(`Work.ORVonNeumann.Rep.hcoord_matOp_apply`); this operator is zero only if the matrix is.

The non-trivial direction is proved with the separating vector `δ₁` of the group von Neumann
algebra (`Work.ORVonNeumann.Rep.delta1_separating`).  Feeding the elementary vector `δ₁` into
the `j`-th summand (`Work.ORVonNeumann.Rep.hdelta m j`) and projecting onto the `i`-th
coordinate, only the `(i, j)`-entry survives, so `matOp A = 0` forces
`(A i j) δ₁ = 0` for all `i, j`, whence `A i j = 0`. -/
theorem matOp_eq_zero_iff {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m : ℕ} (A : Matrix (Fin n) (Fin m) ↥(Work.ORVonNeumann.groupVonNeumann G)) : Work.ORVonNeumann.Rep.matOp (G := G) A = 0 ↔ A = 0 := by
  constructor
  · -- If the operator vanishes, so does every entry of the matrix: test it on `δ₁`.
    intro h
    funext i j
    refine Work.ORVonNeumann.Rep.delta1_separating (A i j) ?_
    -- `matOp A` applied to the vector which is `δ₁` in the `j`-th summand is zero.
    have hmap : Work.ORVonNeumann.Rep.matOp (G := G) A
        (Work.ORVonNeumann.Rep.hdelta (G := G) m j) = 0 := by
      rw [h, zero_apply]
    have h1 : Work.ORVonNeumann.Rep.hcoord (G := G) n i
        (Work.ORVonNeumann.Rep.matOp (G := G) A
          (Work.ORVonNeumann.Rep.hdelta (G := G) m j)) = 0 := by
      rw [hmap, map_zero]
    rw [Work.ORVonNeumann.Rep.hcoord_matOp_apply] at h1
    -- Only the summand `j' = j` contributes, and there `hcoord m j (hdelta m j) = δ₁`.
    rw [Finset.sum_eq_single j] at h1
    · simpa using h1
    · intro j' _ hj'
      rw [Work.ORVonNeumann.Rep.hcoord_hdelta, if_neg hj', map_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · -- Conversely the zero matrix clearly gives the zero operator.
    intro hA
    rw [hA]
    simp [Work.ORVonNeumann.Rep.matOp]

end Work.ORP311
