import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.RankAPI.rk_add_le

namespace Work.Section3

open Matrix Work.ORHughesFree

/-- **Additivity of a Sylvester rank function on orthogonal idempotents.**

If `e₁` and `e₂` are idempotent `n × n` matrices with `e₁ * e₂ = e₂ * e₁ = 0`, then
`rk (e₁ + e₂) = rk e₁ + rk e₂`.

The inequality `≤` is subadditivity (`(SMat2)`).  For `≥` we use the two matrices
`L = [e₁; e₂]` (`2n × n`) and `R = [e₁  e₂]` (`n × 2n`): from `e₁ * (e₁+e₂) = e₁` and
`e₂ * (e₁+e₂) = e₂` one gets the block identity
`L * (e₁ + e₂) * R = diag (e₁, e₂)`, so that
`rk e₁ + rk e₂ = rk (diag (e₁,e₂)) = rk (L (e₁+e₂) R) ≤ rk (L (e₁+e₂)) ≤ rk (e₁+e₂)`
by `(SMat3)` and two applications of `(SMat2)`. -/
theorem rk_add_of_orthogonal_idempotent {R : Type*} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R) {n : ℕ}
    (e₁ e₂ : Matrix (Fin n) (Fin n) R) (h₁ : e₁ * e₁ = e₁) (h₂ : e₂ * e₂ = e₂)
    (h₁₂ : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0) :
    rk.rk n n (e₁ + e₂) = rk.rk n n e₁ + rk.rk n n e₂ := by
  have hE1 : e₁ * (e₁ + e₂) = e₁ := by rw [mul_add, h₁, h₁₂, add_zero]
  have hE2 : e₂ * (e₁ + e₂) = e₂ := by rw [mul_add, h₂₁, h₂, zero_add]
  -- The block identity in the "un-subscripted" (sum-indexed) world.
  have key : (Matrix.fromRows e₁ e₂) * (e₁ + e₂) * (Matrix.fromCols e₁ e₂)
      = Matrix.fromBlocks e₁ 0 0 e₂ := by
    rw [Matrix.fromRows_mul, hE1, hE2, Matrix.fromRows_mul_fromCols, h₁, h₂, h₁₂, h₂₁]
  -- Transfer to `Fin (n + n)`-indexed matrices.
  have h1 : (Matrix.fromRows e₁ e₂).submatrix finSumFinEquiv.symm id * (e₁ + e₂)
      = ((Matrix.fromRows e₁ e₂) * (e₁ + e₂)).submatrix finSumFinEquiv.symm id := by
    have h := Matrix.submatrix_mul_equiv (Matrix.fromRows e₁ e₂) (e₁ + e₂)
      finSumFinEquiv.symm (Equiv.refl (Fin n)) (id : Fin n → Fin n)
    simpa using h
  have h2 : ((Matrix.fromRows e₁ e₂) * (e₁ + e₂)).submatrix finSumFinEquiv.symm id
        * (Matrix.fromCols e₁ e₂).submatrix id finSumFinEquiv.symm
      = ((Matrix.fromRows e₁ e₂) * (e₁ + e₂) * (Matrix.fromCols e₁ e₂)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
    have h := Matrix.submatrix_mul_equiv ((Matrix.fromRows e₁ e₂) * (e₁ + e₂))
      (Matrix.fromCols e₁ e₂) finSumFinEquiv.symm (Equiv.refl (Fin n)) finSumFinEquiv.symm
    simpa using h
  have hLR : (Matrix.fromRows e₁ e₂).submatrix finSumFinEquiv.symm id * (e₁ + e₂)
        * (Matrix.fromCols e₁ e₂).submatrix id finSumFinEquiv.symm
      = blockDiagFin e₁ e₂ := by
    rw [h1, h2, key, blockDiagFin]
  have hle : rk.rk n n e₁ + rk.rk n n e₂ ≤ rk.rk n n (e₁ + e₂) := by
    calc rk.rk n n e₁ + rk.rk n n e₂
        = rk.rk (n + n) (n + n) (blockDiagFin e₁ e₂) := (rk.rk_blockDiag e₁ e₂).symm
      _ = rk.rk (n + n) (n + n)
            ((Matrix.fromRows e₁ e₂).submatrix finSumFinEquiv.symm id * (e₁ + e₂)
              * (Matrix.fromCols e₁ e₂).submatrix id finSumFinEquiv.symm) := by rw [hLR]
      _ ≤ rk.rk (n + n) n
            ((Matrix.fromRows e₁ e₂).submatrix finSumFinEquiv.symm id * (e₁ + e₂)) :=
          rk.rk_mul_le_left _ _
      _ ≤ rk.rk n n (e₁ + e₂) :=
          rk.rk_mul_le_right _ _
  exact le_antisymm (RankAPI.rk_add_le rk e₁ e₂) hle

end Work.Section3
