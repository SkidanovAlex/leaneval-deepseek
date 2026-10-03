/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The block decomposition of the product of two truncations

For matrices `A : Matrix (Fin n) (Fin m) (SkewL U)` and `B : Matrix (Fin m) (Fin k) (SkewL U)`
over the skew Laurent polynomial ring, the product `trunc i A * trunc i B` of the truncations is
the sum over the *intermediate degrees* `v ∈ [0, i)` of the outer products of the row block
`truncBlkRow A i v` with the column block `truncBlkCol B i v`.

Both sides are, entrywise, a sum over the intermediate index `(j, v) ∈ Fin m × Fin i`; the only
content is the reindexing of the summation from `Fin (m * i)` to `Fin m × Fin i` via
`finProdFinEquiv`, together with the definitional unfolding of the truncation and of the two
block matrices.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.TruncDefect

namespace Work.ORHughesFree.NaturalExtension

open Matrix

theorem trunc_mul_eq_sum {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (B : Matrix (Fin m) (Fin k) (SkewL U))
    (i : ℕ) :
    trunc i A * trunc i B =
      ∑ v : Fin i, truncBlkRow A i ((v : ℕ) : ℤ) * truncBlkCol B i ((v : ℕ) : ℤ) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.sum_apply]
  -- The common summand, written with the intermediate index split as `(j, w) ∈ Fin m × Fin i`.
  have hterm : ∀ (j : Fin m) (w : Fin i),
      trunc i A x (finProdFinEquiv (j, w)) * trunc i B (finProdFinEquiv (j, w)) y
        = truncBlkRow A i ((w : ℕ) : ℤ) x j * truncBlkCol B i ((w : ℕ) : ℤ) j y := by
    intro j w
    rw [trunc_apply, trunc_apply, truncBlkRow, truncBlkCol,
      Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_fst,
      Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_snd]
    simp [Matrix.smul_apply]
  -- Reindex the summation over `Fin (m * i)` on the left as a double sum over `Fin m × Fin i`.
  rw [← Equiv.sum_comp finProdFinEquiv
        (fun u : Fin (m * i) => trunc i A x u * trunc i B u y)]
  rw [Fintype.sum_prod_type]
  -- Swap the order of summation on the right, and match the summands.
  rw [show (∑ c : Fin i, ∑ j : Fin m,
        truncBlkRow A i ((c : ℕ) : ℤ) x j * truncBlkCol B i ((c : ℕ) : ℤ) j y)
      = ∑ j : Fin m, ∑ c : Fin i,
        truncBlkRow A i ((c : ℕ) : ℤ) x j * truncBlkCol B i ((c : ℕ) : ℤ) j y
      from Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => hterm j c

end Work.ORHughesFree.NaturalExtension
