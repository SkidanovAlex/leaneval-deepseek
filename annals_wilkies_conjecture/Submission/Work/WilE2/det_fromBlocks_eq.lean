import Mathlib

namespace Work.WilE2

open Matrix

private lemma vecMulVec_rep {n : ℕ} (u v : Fin n → ℝ) :
    Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) v = Matrix.vecMulVec u v := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.replicateCol, Matrix.replicateRow]

private lemma neg_rep_mul_rep {n : ℕ} (u v : Fin n → ℝ) :
    (-(Matrix.replicateCol (Fin 1) u)) * Matrix.replicateRow (Fin 1) v = -Matrix.vecMulVec u v := by
  rw [Matrix.neg_mul, vecMulVec_rep u v]

private lemma neg_rep_mul_neg_one {n : ℕ} (u : Fin n → ℝ) :
    (-(Matrix.replicateCol (Fin 1) u)) * (-1 : Matrix (Fin 1) (Fin 1) ℝ) =
      Matrix.replicateCol (Fin 1) u := by
  rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

theorem det_fromBlocks_eq {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) : (Matrix.fromBlocks P (Matrix.of (fun i (_ : Fin 1) => u i)) (Matrix.of (fun (_ : Fin 1) j => v j)) (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => (-1 : ℝ)))).det = -(P + Matrix.vecMulVec u v).det := by
  have hS : (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => (-1 : ℝ)) : Matrix (Fin 1) (Fin 1) ℝ) = -1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hS]
  change (Matrix.fromBlocks P (Matrix.replicateCol (Fin 1) u) (Matrix.replicateRow (Fin 1) v) (-1)).det =
    -(P + Matrix.vecMulVec u v).det
  have hMN : Matrix.fromBlocks P (Matrix.replicateCol (Fin 1) u) (Matrix.replicateRow (Fin 1) v) (-1) =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-(Matrix.replicateCol (Fin 1) u))
          (0 : Matrix (Fin 1) (Fin n) ℝ) 1 *
        Matrix.fromBlocks (P + Matrix.vecMulVec u v) (0 : Matrix (Fin n) (Fin 1) ℝ)
          (Matrix.replicateRow (Fin 1) v) (-1) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.one_mul, neg_rep_mul_rep u v]
      abel
    · rw [Matrix.one_mul, zero_add, neg_rep_mul_neg_one u]
    · rw [Matrix.zero_mul, Matrix.one_mul, zero_add]
    · rw [Matrix.zero_mul, Matrix.one_mul, zero_add]
  have hdetS : Matrix.det (-1 : Matrix (Fin 1) (Fin 1) ℝ) = -1 := by
    rw [Matrix.det_fin_one]
    simp
  rw [hMN, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, Matrix.det_one, hdetS]
  ring

end Work.WilE2
