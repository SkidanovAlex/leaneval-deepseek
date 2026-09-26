import Mathlib

namespace Work.SG

/-- The Weyl sum `∑ A ∈ P, Aᵀ * A` of a finite family of real square matrices
containing the identity is positive definite: split off the `A = 1` term, which
gives `1` (positive definite), and observe that every remaining term `Aᵀ * A` is
positive semidefinite. -/
theorem weyl_sum_transpose_mul_posDef {n : Type*} [Fintype n] [DecidableEq n]
    (P : Finset (Matrix n n ℝ)) (h1 : (1 : Matrix n n ℝ) ∈ P) :
    Matrix.PosDef (∑ A ∈ P, Matrix.transpose A * A) := by
  classical
  have hsum : (∑ A ∈ P, Matrix.transpose A * A) =
      (1 : Matrix n n ℝ) + ∑ A ∈ P.erase 1, Matrix.transpose A * A := by
    conv_lhs => rw [← Finset.insert_erase h1]
    rw [Finset.sum_insert (Finset.notMem_erase _ _), Matrix.transpose_one, one_mul]
  rw [hsum]
  refine Matrix.PosDef.add_posSemidef Matrix.PosDef.one ?_
  exact Matrix.posSemidef_sum _ (fun A _ => by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A)

end Work.SG
