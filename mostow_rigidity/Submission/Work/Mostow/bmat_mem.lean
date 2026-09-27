import Mathlib
import Submission.Work.Mostow.bmatBlocks

/-!
# `bmat v ∈ O(n,1)`

The hyperbolic boost `bmat v` (sending `e₀ = hlift 0` to `hlift v`) lies in `O(n,1)`,
i.e. `(bmat v)ᵀ J (bmat v) = J` and `(bmat v) J (bmat v)ᵀ = J` for `J = pmOneMat = diag(1,…,−1)`.
Both identities are the four block computations collected in `bmatBlocks`
(`bA_gram`, `bA_bB_orth`, `bB_bA_orth`, `bB_gram`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Topology
open Matrix

noncomputable section

variable {n : ℕ}

/-- `(bmat v)ᵀ J (bmat v) = J`. -/
theorem bmat_conj_col (v : E n) :
    (bmat v)ᵀ * pmOneMat * bmat v = pmOneMat := by
  have hJ : pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ) =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) 0 0
        (-1 : Matrix (Fin 1) (Fin 1) ℝ) := rfl
  rw [bmat_eq_blocks, hJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [sub_eq_add_neg] using bA_gram v
  · simpa only [sub_eq_add_neg] using bA_bB_orth v
  · simpa only [sub_eq_add_neg] using bB_bA_orth v
  · simpa only [sub_eq_add_neg] using bB_gram v

/-- `(bmat v) J (bmat v)ᵀ = J`. -/
theorem bmat_conj_row (v : E n) :
    bmat v * pmOneMat * (bmat v)ᵀ = pmOneMat := by
  have hJ : pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ) =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) 0 0
        (-1 : Matrix (Fin 1) (Fin 1) ℝ) := rfl
  rw [bmat_eq_blocks, hJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [transpose_bA, transpose_bB, transpose_bC, bB_mul_bC, sub_eq_add_neg]
      using bA_gram v
  · simpa only [transpose_bA, transpose_bB, transpose_bC, transpose_bD, sub_eq_add_neg]
      using bA_bB_orth v
  · simpa only [transpose_bA, transpose_bB, transpose_bC, transpose_bD, sub_eq_add_neg]
      using bB_bA_orth v
  · simpa only [transpose_bB, transpose_bC, transpose_bD, sub_eq_add_neg] using bB_gram v

theorem bmat_mem (n : ℕ) (v : Submission.Mostow.E n) :
    Work.Mostow.bmat v ∈ Submission.Mostow.O1 n := by
  refine (mem_unitary_iff (MatrixSum.ofMatrix (bmat v))).2 ⟨?_, ?_⟩
  · change (bmat v)ᵀ * pmOneMat * bmat v = pmOneMat
    exact bmat_conj_col v
  · change bmat v * pmOneMat * (bmat v)ᵀ = pmOneMat
    exact bmat_conj_row v

end

end Work.Mostow
