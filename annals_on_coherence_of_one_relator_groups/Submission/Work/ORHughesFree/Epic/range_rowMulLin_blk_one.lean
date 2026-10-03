/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The row space of the block matrix `[[A, 0], [0, 1]]`

For a matrix `A : m × n` over a ring `R` and a natural number `n'`, let
`blkOne A = RankAPI.blk A 0 0 (1 : Matrix (Fin n') (Fin n') R)` be the block matrix
`[[A, 0], [0, 1]]`, with `m + n'` rows and `n + n'` columns.  Writing a vector of `R^{m+n'}` as a
pair `(x, y) ∈ R^m × R^{n'}` by means of `CokerIso.sumProdEquiv`, its row product with
`blkOne A` is `(x ᵥ* A, y)`: the second block row of `[[A, 0], [0, 1]]` kills the first block of
the vector and keeps the second one unchanged.

Consequently the row space of `blkOne A` is the product of the row space of `A` with the whole
of `R^{n'}`, transported along `CokerIso.sumProdEquiv`:

* `rowMulLin_blkOne` is the pointwise computation of the row map of `blkOne A`, in the form
  `(E R m n' (x, y)) ᵥ* blkOne A = E R n n' (x ᵥ* A, y)`;
* `rowMulLin_blkOne_symm` is the same computation expressed with the inverse of `E R m n'`,
  which is the form needed to describe the image of the row map;
* `range_rowMulLin_blk_one` is the resulting identity of row spaces.

These are the `[[A, 0], [0, 1]]` counterparts of `Epic/range_rowMulLin_blkB`, and are the two
row-space computations used in Malcolmson's strengthened Schanuel lemma
(`Epic/rk_blkM_eq_of_relations`).
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.CokerIsoDefs

namespace Work.ORHughesFree.Epic

open Matrix

variable {R : Type*}

/-- The block matrix `[[A, 0], [0, 1]]`: `A` has `m` rows and `n` columns, the identity block has
`n'` rows and columns, so that the matrix has `m + n'` rows and `n + n'` columns. -/
def blkOne [Ring R] {m n n' : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin (m + n')) (Fin (n + n')) R :=
  RankAPI.blk A 0 0 (1 : Matrix (Fin n') (Fin n') R)

/-- The row map of `blkOne A` computed on a pair of vectors: for `x : R^m` and `y : R^{n'}`,
`v ᵥ* [[A, 0], [0, 1]] = (x ᵥ* A, y)` where `v = sumProdEquiv R m n' (x, y)`. -/
theorem rowMulLin_blkOne [Ring R] {m n n' : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (x : Fin m → R) (y : Fin n' → R) :
    rowMulLin (blkOne A) (CokerIso.sumProdEquiv R m n' (x, y))
      = CokerIso.sumProdEquiv R n n' (rowMulLin A x, y) := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    show (∑ k, CokerIso.sumProdEquiv R m n' (x, y) k * blkOne A k (Fin.castAdd n' i)) = _
    rw [← Equiv.sum_comp finSumFinEquiv
      (fun k => CokerIso.sumProdEquiv R m n' (x, y) k * blkOne A k (Fin.castAdd n' i))]
    rw [Fintype.sum_sum_type]
    simp [blkOne, RankAPI.blk, CokerIso.sumProdEquiv, rowMulLin, Matrix.submatrix_apply]
  · intro i
    show (∑ k, CokerIso.sumProdEquiv R m n' (x, y) k * blkOne A k (Fin.natAdd n i)) = _
    rw [← Equiv.sum_comp finSumFinEquiv
      (fun k => CokerIso.sumProdEquiv R m n' (x, y) k * blkOne A k (Fin.natAdd n i))]
    rw [Fintype.sum_sum_type]
    simp [blkOne, RankAPI.blk, CokerIso.sumProdEquiv, rowMulLin, Matrix.submatrix_apply,
      Matrix.one_apply]

/-- `rowMulLin_blkOne` with the pair of blocks recovered from the vector itself: the row map of
`blkOne A` sends `v` to `(x ᵥ* A, y)` where `(x, y) = (sumProdEquiv R m n').symm v`. -/
theorem rowMulLin_blkOne_symm [Ring R] {m n n' : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (v : Fin (m + n') → R) :
    rowMulLin (blkOne A) v
      = CokerIso.sumProdEquiv R n n'
          (rowMulLin A ((CokerIso.sumProdEquiv R m n').symm v).1,
           ((CokerIso.sumProdEquiv R m n').symm v).2) := by
  conv_lhs => rw [← LinearEquiv.apply_symm_apply (CokerIso.sumProdEquiv R m n') v]
  rw [← Prod.eta ((CokerIso.sumProdEquiv R m n').symm v)]
  rw [rowMulLin_blkOne]

/-- The row space of the block matrix `[[A, 0], [0, 1]]` is the row space of `A` in the first block
and the whole second block. -/
theorem range_rowMulLin_blk_one {R : Type*} [Ring R] {m n n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) :
    LinearMap.range (Work.ORHughesFree.Epic.rowMulLin
        (Work.ORHughesFree.RankAPI.blk A 0 0 (1 : Matrix (Fin n') (Fin n') R)))
      = Submodule.map (Work.ORHughesFree.Epic.CokerIso.sumProdEquiv R n n').toLinearMap
          (Submodule.prod (LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A)) ⊤) := by
  change LinearMap.range (rowMulLin (blkOne A)) = _
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hz
    refine Submodule.mem_map.mpr ⟨(rowMulLin A ((CokerIso.sumProdEquiv R m n').symm v).1,
      ((CokerIso.sumProdEquiv R m n').symm v).2), ?_, ?_⟩
    · exact Submodule.mem_prod.mpr ⟨LinearMap.mem_range.mpr ⟨_, rfl⟩, Submodule.mem_top⟩
    · exact (rowMulLin_blkOne_symm A v).symm
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨a, b⟩ := w
    obtain ⟨hwa, -⟩ := Submodule.mem_prod.mp hw
    have hwa' : a ∈ LinearMap.range (rowMulLin A) := hwa
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hwa'
    exact LinearMap.mem_range.mpr ⟨CokerIso.sumProdEquiv R m n' (x, b),
      by rw [← hx]; exact rowMulLin_blkOne A x b⟩

end Work.ORHughesFree.Epic
