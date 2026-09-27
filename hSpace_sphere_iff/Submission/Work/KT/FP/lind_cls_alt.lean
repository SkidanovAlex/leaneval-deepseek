import Mathlib
import Submission.Work.KT.FP.LindDefs

/-!
# `Work.KT.FP.lind_cls_alt` — the `K₀`-class of the projection `diag(1, P, 0)`

The projection of the linearisation of `(1-P) + z·P` is the block matrix `diag(1, P, 0)`, whose
class in `K₀ C(X, ℂ)` is `[1_n] + [P] = [1_n ⊕ P]`.

The projection and the block sum `1_n ⊕ P` are Murray–von Neumann equivalent by the rectangular
witnesses `a = [[1,0,0],[0,P,0]]` (`2n × 3n`) and `b = [[1,0],[0,1],[0,0]]` (`3n × 2n`):
`b·a = diag(1,P,0)` and `a·b = diag(1,P)`.  Since `Mat.MvN` does not require the two matrices to
have the same size, `cls_eq_of_mvN` applies directly, with no size bookkeeping.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable (X : Type) [TopologicalSpace X] (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ))

/-- The `2n × 3n` witness `[[1,0,0],[0,P,0]]` (block rows `Fin n ⊕ Fin n`, block columns
`Fin 3 × Fin n`). -/
def lindMvNa : Matrix (Fin n ⊕ Fin n) (Fin 3 × Fin n) C(X, ℂ) :=
  fun i j => match i with
    | Sum.inl a => (if (j.1 : ℕ) = 0 then (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) else 0) a j.2
    | Sum.inr a => (if (j.1 : ℕ) = 1 then P else 0) a j.2

/-- The `3n × 2n` witness `[[1,0],[0,1],[0,0]]`. -/
def lindMvNb : Matrix (Fin 3 × Fin n) (Fin n ⊕ Fin n) C(X, ℂ) :=
  fun i j => match j with
    | Sum.inl b => (if (i.1 : ℕ) = 0 then (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) else 0) i.2 b
    | Sum.inr b => (if (i.1 : ℕ) = 1 then (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) else 0) i.2 b

@[simp] lemma lindMvNa_inl (a : Fin n) (j : Fin 3 × Fin n) :
    lindMvNa X n P (Sum.inl a) j
      = (if (j.1 : ℕ) = 0 then (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) else 0) a j.2 := rfl

@[simp] lemma lindMvNa_inr (a : Fin n) (j : Fin 3 × Fin n) :
    lindMvNa X n P (Sum.inr a) j
      = (if (j.1 : ℕ) = 1 then P else 0) a j.2 := rfl

@[simp] lemma lindMvNb_inl (i : Fin 3 × Fin n) (b : Fin n) :
    lindMvNb X n (i) (Sum.inl b)
      = (if (i.1 : ℕ) = 0 then (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) else 0) i.2 b := rfl

@[simp] lemma lindMvNb_inr (i : Fin 3 × Fin n) (b : Fin n) :
    lindMvNb X n (i) (Sum.inr b)
      = (if (i.1 : ℕ) = 1 then (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) else 0) i.2 b := rfl

/-- `b·a = diag(1, P, 0)` (the product of the two rectangular witnesses). -/
lemma lindMvNb_mul_lindMvNa :
    lindMvNb X n * lindMvNa X n P = blockMat X n (lindC X n P) := by
  ext ⟨i, c⟩ ⟨j, b⟩
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  fin_cases i <;> fin_cases j <;>
    simp [lindMvNa, lindMvNb, blockMat, lindC, Matrix.one_apply]

/-- `a·b = diag(1, P)`. -/
lemma lindMvNa_mul_lindMvNb :
    lindMvNa X n P * lindMvNb X n
      = Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 P := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
  rcases i with a | a <;> rcases j with b | b <;>
    simp [lindMvNa, lindMvNb, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

/-- **The class of the projection.** -/
theorem lind_cls_alt (hP : P * P = P) :
    cls (⟨3 * n, Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindC X n P))⟩
      : Mat C(X, ℂ))
      = cls (Mat.sum (Mat.one C(X, ℂ) n) (⟨n, P⟩ : Mat C(X, ℂ))) := by
  have hone : (Mat.one C(X, ℂ) n).IsIdem := by
    unfold Mat.IsIdem Mat.one
    exact Matrix.mul_one 1
  have hP' : Mat.IsIdem (⟨n, P⟩ : Mat C(X, ℂ)) := hP
  have hq : (Mat.sum (Mat.one C(X, ℂ) n) (⟨n, P⟩ : Mat C(X, ℂ))).IsIdem :=
    Mat.sum_idem hone hP'
  have hp : Mat.IsIdem (⟨3 * n, Matrix.reindex finProdFinEquiv finProdFinEquiv
      (blockMat X n (lindC X n P))⟩ : Mat C(X, ℂ)) := by
    show Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindC X n P))
        * Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindC X n P))
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindC X n P))
    rw [reindexMat_mul, ← blockMat_mul, lindC_idem X n P hP]
  have hmvN : Mat.MvN (⟨3 * n, Matrix.reindex finProdFinEquiv finProdFinEquiv
      (blockMat X n (lindC X n P))⟩ : Mat C(X, ℂ))
      (Mat.sum (Mat.one C(X, ℂ) n) (⟨n, P⟩ : Mat C(X, ℂ))) := by
    refine ⟨Matrix.reindex finSumFinEquiv finProdFinEquiv (lindMvNa X n P),
      Matrix.reindex finProdFinEquiv finSumFinEquiv (lindMvNb X n), ?_, ?_⟩
    · show Matrix.reindex finProdFinEquiv finSumFinEquiv (lindMvNb X n)
          * Matrix.reindex finSumFinEquiv finProdFinEquiv (lindMvNa X n P)
        = Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindC X n P))
      rw [Work.KT.reindexMul finProdFinEquiv finSumFinEquiv finProdFinEquiv
        (lindMvNb X n) (lindMvNa X n P), lindMvNb_mul_lindMvNa]
    · show Matrix.reindex finSumFinEquiv finProdFinEquiv (lindMvNa X n P)
          * Matrix.reindex finProdFinEquiv finSumFinEquiv (lindMvNb X n)
        = Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 P)
      rw [Work.KT.reindexMul finSumFinEquiv finProdFinEquiv finSumFinEquiv
        (lindMvNa X n P) (lindMvNb X n), lindMvNa_mul_lindMvNb]
  exact cls_eq_of_mvN hp hq hmvN

end

end Work.KT.FP
