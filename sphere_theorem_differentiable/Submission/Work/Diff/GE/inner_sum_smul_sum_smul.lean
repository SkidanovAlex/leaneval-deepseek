import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

/-- **A bilinear form of two finite linear combinations is a matrix product.**

For a continuous bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`, vectors `u : Fin n → V` with Gram matrix
`Mm` (`Mm k l = B (u k) (u l)`) and matrices `A`, `C`, the pairing of the two combinations
`∑ k, A k i • u k` and `∑ l, C l j • u l` is the `(i,j)` entry of the matrix product
`Aᵀ * Mm * C`.

Proof: expand both arguments by `map_sum`/`map_smul` for the continuous linear maps `B` and `B x`,
then identify the resulting double sum with `(Aᵀ * Mm * C) i j` using `Matrix.mul_apply` and
`Matrix.transpose_apply` (with `Finset.sum_comm`, `Finset.mul_sum`/`Finset.sum_mul` to rearrange). -/
theorem inner_sum_smul_sum_smul {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u : Fin n → V) (Mm A C : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ k l, Mm k l = B (u k) (u l)) (i j : Fin n) :
    B (∑ k, A k i • u k) (∑ l, C l j • u l) = (A.transpose * Mm * C) i j := by
  -- Expand the two matrix-product entries and both linear combinations.
  simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_smul,
    FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- Rewrite `B (u k) (u l)` back to the Gram entry `Mm k l`.
  simp only [← hM, Finset.mul_sum, Finset.sum_mul]
  -- Both sides are now double sums of the same products; match them and commute the scalars.
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end Work.Diff.GE
