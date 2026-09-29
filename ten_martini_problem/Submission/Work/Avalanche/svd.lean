import Mathlib
import Submission.Work.TMC7Core.Avalanche.rift
import Submission.Work.Avalanche.gram_spectral_diagonal
import Submission.Work.Avalanche.orthonormal_columns_unitary

/-!
# Singular value decomposition of a `2 × 2` complex matrix of determinant one

For `X : Matrix (Fin 2) (Fin 2) ℂ` with `X.det = 1` we produce unitary matrices `U`, `V` and
positive reals `a`, `b` with `a * b = 1` and `X = U * diag(a, b) * Vᴴ`.

The proof diagonalizes the Gram matrix `Xᴴ * X` by a unitary `V` (spectral theorem for the
positive definite Hermitian matrix `Xᴴ * X`), giving `Xᴴ * X = V * diag d * Vᴴ` with `d i > 0`
and `∏ d i = det (Xᴴ * X) = 1`; then `Y := X * V` satisfies `Yᴴ * Y = diag d`, so normalizing the
columns of `Y` by `1 / √(d i)` yields the unitary factor `U` with `Y = U * diag √d`.
-/

namespace Work.Avalanche

open Matrix

lemma svd (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.det = 1) :
    ∃ (U V : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℝ),
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      V.conjTranspose * V = 1 ∧ V * V.conjTranspose = 1 ∧
      0 < a ∧ 0 < b ∧ a * b = 1 ∧
      X = U * Matrix.diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] * V.conjTranspose := by
  obtain ⟨V, d, hV1, hV2, hd, hdprod, hgram⟩ := gram_spectral_diagonal X hX
  -- `Y := X * V` has `Yᴴ * Y = diagonal d`.
  have hY : (X * V).conjTranspose * (X * V) =
      Matrix.diagonal (fun i : Fin 2 => ((d i : ℝ) : ℂ)) := by
    rw [Matrix.conjTranspose_mul]
    calc (V.conjTranspose * X.conjTranspose) * (X * V)
        = V.conjTranspose * (X.conjTranspose * X) * V := by simp only [Matrix.mul_assoc]
      _ = V.conjTranspose *
            (V * Matrix.diagonal (fun i : Fin 2 => ((d i : ℝ) : ℂ)) * V.conjTranspose) * V := by
            rw [hgram]
      _ = Matrix.diagonal (fun i : Fin 2 => ((d i : ℝ) : ℂ)) := by
            simp only [Matrix.mul_assoc]
            rw [hV1, Matrix.mul_one, ← Matrix.mul_assoc, hV1, Matrix.one_mul]
  -- Normalize the columns of `Y`.
  obtain ⟨U, hU1, hU2, hYU⟩ := orthonormal_columns_unitary (X * V) d hd hY
  refine ⟨U, V, Real.sqrt (d 0), Real.sqrt (d 1), hU1, hU2, hV1, hV2, ?_, ?_, ?_, ?_⟩
  · exact Real.sqrt_pos.mpr (hd 0)
  · exact Real.sqrt_pos.mpr (hd 1)
  · have hprod : d 0 * d 1 = 1 := by rw [← Fin.prod_univ_two d]; exact hdprod
    rw [← Real.sqrt_mul (le_of_lt (hd 0)) (d 1), hprod, Real.sqrt_one]
  · have hdiag : Matrix.diagonal (fun i : Fin 2 => ((Real.sqrt (d i) : ℝ) : ℂ))
        = Matrix.diagonal ![((Real.sqrt (d 0) : ℝ) : ℂ), ((Real.sqrt (d 1) : ℝ) : ℂ)] := by
      congr 1
      funext i
      fin_cases i <;> simp
    have hXX : X = U * Matrix.diagonal (fun i : Fin 2 => ((Real.sqrt (d i) : ℝ) : ℂ)) *
        V.conjTranspose := by
      calc X = X * V * V.conjTranspose := by rw [Matrix.mul_assoc, hV2, Matrix.mul_one]
        _ = U * Matrix.diagonal (fun i : Fin 2 => ((Real.sqrt (d i) : ℝ) : ℂ)) *
              V.conjTranspose := by rw [hYU]
    rw [hXX, hdiag]

end Work.Avalanche
