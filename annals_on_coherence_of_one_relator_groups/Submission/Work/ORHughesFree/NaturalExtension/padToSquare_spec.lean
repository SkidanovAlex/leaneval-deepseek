import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.ampDefs
import Submission.Work.ORHughesFree.RankAPI.rk_reindex

universe u

namespace Work.ORHughesFree.NaturalExtension

/-- Every entry of the block diagonal matrix `blockDiagFin A 0` is either `0` or an entry of `A`.
Consequently the property "all negative coefficients vanish" passes from `A` to `blockDiagFin A 0`. -/
private lemma coeffElt_blockDiagFin_zero {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL R))
    (hA : ∀ (i : Fin n) (j : Fin m) (k : ℤ), k < 0 → coeffElt (A i j) k = 0)
    (i : Fin (n + m)) (j : Fin (m + n)) (k : ℤ) (hk : k < 0) :
    coeffElt (blockDiagFin A (0 : Matrix (Fin m) (Fin n) (SkewL R)) i j) k = 0 := by
  -- the entry of `blockDiagFin A 0` at `(i, j)` is `A a b` when both indices lie in the
  -- top-left block, and `0` otherwise
  rcases hi : finSumFinEquiv.symm i with a | a <;>
    rcases hj : finSumFinEquiv.symm j with b | b
  · have h : blockDiagFin A (0 : Matrix (Fin m) (Fin n) (SkewL R)) i j = A a b := by
      simp only [blockDiagFin, Matrix.submatrix_apply, hi, hj]
      exact Matrix.fromBlocks_apply₁₁ A 0 0 0 a b
    rw [h]
    exact hA a b k hk
  · have h : blockDiagFin A (0 : Matrix (Fin m) (Fin n) (SkewL R)) i j = 0 := by
      simp only [blockDiagFin, Matrix.submatrix_apply, hi, hj]
      exact Matrix.fromBlocks_apply₁₂ A 0 0 0 a b
    rw [h]
    simp [coeffElt]
  · have h : blockDiagFin A (0 : Matrix (Fin m) (Fin n) (SkewL R)) i j = 0 := by
      simp only [blockDiagFin, Matrix.submatrix_apply, hi, hj]
      exact Matrix.fromBlocks_apply₂₁ A 0 0 0 a b
    rw [h]
    simp [coeffElt]
  · have h : blockDiagFin A (0 : Matrix (Fin m) (Fin n) (SkewL R)) i j = 0 := by
      simp only [blockDiagFin, Matrix.submatrix_apply, hi, hj]
      exact Matrix.fromBlocks_apply₂₂ A 0 0 0 a b
    rw [h]
    simp [coeffElt]

theorem padToSquare_spec {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (rk : Work.ORHughesFree.SylvesterRank (Work.ORHughesFree.NaturalExtension.SkewL R))
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) (Work.ORHughesFree.NaturalExtension.SkewL R))
    (hA : ∀ (i : Fin n) (j : Fin m) (k : ℤ), k < 0 → Work.ORHughesFree.NaturalExtension.coeffElt (A i j) k = 0) :
    (∀ (i j : Fin (n + m)) (k : ℤ), k < 0 →
        Work.ORHughesFree.NaturalExtension.coeffElt (Work.ORHughesFree.NaturalExtension.padToSquare A i j) k = 0) ∧
      rk.rk (n + m) (n + m) (Work.ORHughesFree.NaturalExtension.padToSquare A) = rk.rk n m A := by
  constructor
  · -- first component: `padToSquare A` is `blockDiagFin A 0` with reindexed columns
    intro i j k hk
    rw [show padToSquare A i j
        = blockDiagFin A (0 : Matrix (Fin m) (Fin n) (SkewL R)) i
            ((finCongr (Nat.add_comm m n)).symm j) from rfl]
    exact coeffElt_blockDiagFin_zero A hA i _ k hk
  · -- second component: the rank is unchanged, since `padToSquare A` is a reindexing of the
    -- block diagonal matrix `A ⊕ 0` and `rk 0 = 0`
    have hpad : padToSquare A
        = Matrix.reindex (Equiv.refl (Fin (n + m))) (finCongr (Nat.add_comm m n))
            (blockDiagFin A (0 : Matrix (Fin m) (Fin n) (SkewL R))) := rfl
    have h1 : rk.rk (n + m) (n + m) (padToSquare A)
        = rk.rk (n + m) (m + n)
            (blockDiagFin A (0 : Matrix (Fin m) (Fin n) (SkewL R))) := by
      rw [hpad]
      exact Work.ORHughesFree.RankAPI.rk_reindex rk (Equiv.refl (Fin (n + m)))
        (finCongr (Nat.add_comm m n)) _
    have h2 : rk.rk (n + m) (m + n)
        (blockDiagFin A (0 : Matrix (Fin m) (Fin n) (SkewL R))) = rk.rk n m A := by
      have h := rk.rk_blockDiag A (0 : Matrix (Fin m) (Fin n) (SkewL R))
      rw [h, rk.rk_zero, add_zero]
    rw [h1, h2]

end Work.ORHughesFree.NaturalExtension
