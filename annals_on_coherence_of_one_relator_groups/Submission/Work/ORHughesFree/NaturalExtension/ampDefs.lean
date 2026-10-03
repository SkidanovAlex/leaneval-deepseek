/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Amplification of Sylvester rank functions

Auxiliary definitions for the *amplification* argument of [JZLA20, §3]: if `R` is a ring with a
Sylvester rank function `rk`, then the "block" assignment

  `A ↦ rk (flattenBlocks A) / N`

on `k × l` matrices of `N × N` blocks over `R` is again a Sylvester rank function on the matrix
ring `Mat_N(R)` (`MatrixBlocks.exists_sylvesterRank_matrix_unfaithful`), the **amplified** rank
function `amplifiedRank rk N hN`.

Combined with the entrywise ring isomorphism
`skewMatrixEquiv : Mat_N(R)[t^{±1};τ] ≃+* Mat_N(R[t^{±1};τ])` of `skewMatrixRingEquiv`, this
transports a natural extension `rkE` of `rk` to `R[t^{±1};τ]` to a natural extension of the
amplified `rk` to `Mat_N(R)[t^{±1};τ]`.  In particular, if two Sylvester rank functions on
`R[t^{±1};τ]` are natural extensions of the same `rk`, then the amplified rank functions on
`Mat_N(R)[t^{±1};τ]` are natural extensions of the same `amplifiedRank rk N hN`, so the `1 × 1`
case of uniqueness applied over the ring `Mat_N(R)` yields uniqueness on `N × N` matrices over
`R` — and an arbitrary `n × m` matrix is padded to a square one.

## Main definitions

* `amplifiedRank` : the rank function `A ↦ rk (flattenBlocks A) / N` on `Mat_N(R)`;
* `skewMatrixEquiv` : the entrywise isomorphism `Mat_N(R)[t^{±1};τ] ≃+* Mat_N(R[t^{±1};τ])`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.skewMatrixRingEquiv
import Submission.Work.ORHughesFree.NaturalExtension.matrixMulSemiringAction
import Submission.Work.ORHughesFree.MatrixBlocks.exists_sylvesterRank_matrix_unfaithful

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- **The amplified Sylvester rank function.**  For a Sylvester rank function `rk` on a ring `U`
and `N > 0`, the assignment `A ↦ rk (flattenBlocks A) / N` on matrices of `N × N` blocks is a
Sylvester rank function on the matrix ring `Mat_N(U)`. -/
noncomputable def amplifiedRank {U : Type u} [Ring U] (rk : SylvesterRank U) (N : ℕ)
    (hN : 0 < N) : SylvesterRank (Matrix (Fin N) (Fin N) U) :=
  (MatrixBlocks.exists_sylvesterRank_matrix_unfaithful rk N hN).choose

/-- The defining formula of the amplified rank function. -/
theorem amplifiedRank_apply {U : Type u} [Ring U] (rk : SylvesterRank U) (N : ℕ)
    (hN : 0 < N) (k l : ℕ) (A : Matrix (Fin k) (Fin l) (Matrix (Fin N) (Fin N) U)) :
    (amplifiedRank rk N hN).rk k l A
      = rk.rk (k * N) (l * N) (flattenBlocks A) / (N : ℝ) :=
  (MatrixBlocks.exists_sylvesterRank_matrix_unfaithful rk N hN).choose_spec k l A

/-- **The entrywise isomorphism `Mat_N(R)[t^{±1};τ] ≃+* Mat_N(R[t^{±1};τ])`**, obtained from the
coefficient formula `skewMatrixToHom_coeff`. -/
noncomputable def skewMatrixEquiv (R : Type u) [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (N : ℕ) :
    SkewMonoidAlgebra (Matrix (Fin N) (Fin N) R) (Multiplicative ℤ) ≃+*
      Matrix (Fin N) (Fin N) (SkewMonoidAlgebra R (Multiplicative ℤ)) :=
  RingEquiv.ofBijective (skewMatrixToHom R N)
    ⟨skewMatrixToHom_injective R N, skewMatrixToHom_surjective R N⟩

theorem skewMatrixEquiv_apply (R : Type u) [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (N : ℕ) (x : SkewMonoidAlgebra (Matrix (Fin N) (Fin N) R) (Multiplicative ℤ)) :
    skewMatrixEquiv R N x = skewMatrixToHom R N x := rfl

/-- The value of `skewMatrixEquiv` on a monomial `A · t^m`. -/
theorem skewMatrixEquiv_single (R : Type u) [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (N : ℕ) (m : Multiplicative ℤ) (A : Matrix (Fin N) (Fin N) R) :
    skewMatrixEquiv R N (SkewMonoidAlgebra.single m A) =
      A.map (SkewMonoidAlgebra.single m) :=
  skewMatrixToHom_single R N m A

/-- **Padding a matrix to a square one.**  For `A : Matrix (Fin n) (Fin m) (SkewL R)` the block
diagonal matrix `A ⊕ 0` has `n + m` rows and `m + n` columns; reindexing the columns by
`m + n = n + m` gives the square matrix `padToSquare A`. -/
noncomputable def padToSquare {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL R)) :
    Matrix (Fin (n + m)) (Fin (n + m)) (SkewL R) :=
  (blockDiagFin A (0 : Matrix (Fin m) (Fin n) (SkewL R))).submatrix id
    (finCongr (Nat.add_comm m n)).symm

end Work.ORHughesFree.NaturalExtension
