import Mathlib.Analysis.InnerProductSpace.GramMatrix

namespace Commons.LinearAlgebra.GramMatrix

open scoped BigOperators
open Finset

/-- The Gram matrix of the linear combinations of a family of vectors, with
coefficient matrix `C`, is the congruence `C.transpose * gram b * C`. -/
theorem gram_of_linComb {n r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin n → E) (C : Matrix (Fin n) (Fin r) ℝ) :
    Matrix.gram ℝ (fun j : Fin r => ∑ i : Fin n, C i j • b i) =
      C.transpose * Matrix.gram ℝ b * C := by
  ext j k
  rw [Matrix.gram_apply]
  rw [← Matrix.star_dotProduct_gram_mulVec (𝕜 := ℝ) (v := b) (x := fun i => C i j)
      (y := fun i => C i k)]
  calc
    (star (fun i : Fin n => C i j) ⬝ᵥ (Matrix.gram ℝ b).mulVec (fun i => C i k))
        = ∑ i : Fin n, C i j * (∑ l : Fin n, (Matrix.gram ℝ b) i l * C l k) := by
            simp [dotProduct, Pi.star_apply, star_trivial, Matrix.mulVec]
    _ = (C.transpose * Matrix.gram ℝ b * C) j k := by
            simp only [Matrix.mul_apply, Matrix.transpose_apply]
            simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            rw [Finset.sum_comm]

end Commons.LinearAlgebra.GramMatrix