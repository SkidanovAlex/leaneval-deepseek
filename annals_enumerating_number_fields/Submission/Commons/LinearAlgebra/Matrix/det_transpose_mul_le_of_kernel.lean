import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef

namespace Commons.LinearAlgebra.Matrix

/-- **Bordered Gram determinant identity.**
Let `E` be a `(k+n) x (k+n)` real matrix, `B` an `n x (k+n)` real matrix and `S` an `n x n`
real matrix such that `B * E` vanishes on the first `k` columns and equals `S` on the last `n`
columns. Writing `G := Eᵀ E` and `G₁₁` for its top-left `k x k` block, one has

`det G₁₁ * det (B * Bᵀ) * (det E)^2 = (det G₁₁)^2 * (det S)^2`.

This is the algebraic core of `det_transpose_mul_le_of_kernel`: applying it with `det E = ±1`
identifies the Gram determinant of the rows of `B` with `(det S)^2` times the Gram determinant of
the first `k` columns of `E`. The proof borders `E` by the block row `[E₁₁ᵀ | B]` (a square
matrix whose determinant can be evaluated in two ways, using `det A² = det (A Aᵀ)` and
`det_fromBlocks_zero₂₁`). -/
lemma det_transpose_mul_mul_sq {k n : ℕ}
    (B : Matrix (Fin n) (Fin k ⊕ Fin n) ℝ)
    (E : Matrix (Fin k ⊕ Fin n) (Fin k ⊕ Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hBE : ∀ (l : Fin n) (a : Fin k ⊕ Fin n),
      (B * E) l a = Sum.elim (fun _ : Fin k => (0 : ℝ)) (fun j : Fin n => S l j) a) :
    ((Matrix.transpose E * E).submatrix Sum.inl Sum.inl).det *
        (B * Matrix.transpose B).det * E.det ^ 2 =
      ((Matrix.transpose E * E).submatrix Sum.inl Sum.inl).det ^ 2 * S.det ^ 2 := by
  let E11 : Matrix (Fin k) (Fin k) ℝ := E.submatrix Sum.inl Sum.inl
  let E12 : Matrix (Fin k) (Fin n) ℝ := E.submatrix Sum.inl Sum.inr
  let E21 : Matrix (Fin n) (Fin k) ℝ := E.submatrix Sum.inr Sum.inl
  let E22 : Matrix (Fin n) (Fin n) ℝ := E.submatrix Sum.inr Sum.inr
  let B1 : Matrix (Fin n) (Fin k) ℝ := B.submatrix id Sum.inl
  let B2 : Matrix (Fin n) (Fin n) ℝ := B.submatrix id Sum.inr
  let G11 : Matrix (Fin k) (Fin k) ℝ := Matrix.transpose E11 * E11 + Matrix.transpose E21 * E21
  let G12 : Matrix (Fin k) (Fin n) ℝ := Matrix.transpose E11 * E12 + Matrix.transpose E21 * E22
  let M : Matrix (Fin k ⊕ Fin n) (Fin k ⊕ Fin n) ℝ :=
    Matrix.fromBlocks (Matrix.transpose E11) (Matrix.transpose E21) B1 B2
  have hEblocks : E = Matrix.fromBlocks E11 E12 E21 E22 := by
    ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
  have hEtr : Matrix.transpose E =
      Matrix.fromBlocks (Matrix.transpose E11) (Matrix.transpose E21)
        (Matrix.transpose E12) (Matrix.transpose E22) := by
    ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
  have hBL : B1 * E11 + B2 * E21 = 0 := by
    ext j i
    have h1 : (B1 * E11 + B2 * E21) j i = (B * E) j (Sum.inl i) := by
      simp only [B1, B2, E11, E21, Matrix.add_apply, Matrix.mul_apply, Matrix.submatrix_apply,
        Fintype.sum_sum_type, id_eq]
    rw [h1, hBE j (Sum.inl i)]
    rfl
  have hBR : B1 * E12 + B2 * E22 = S := by
    ext j i
    have h1 : (B1 * E12 + B2 * E22) j i = (B * E) j (Sum.inr i) := by
      simp only [B1, B2, E12, E22, Matrix.add_apply, Matrix.mul_apply, Matrix.submatrix_apply,
        Fintype.sum_sum_type, id_eq]
    rw [h1, hBE j (Sum.inr i)]
    rfl
  have hBB : B1 * Matrix.transpose B1 + B2 * Matrix.transpose B2 =
      B * Matrix.transpose B := by
    ext j j'
    simp only [B1, B2, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply, Fintype.sum_sum_type, id_eq]
  have hME : M * E = Matrix.fromBlocks G11 G12 0 S := by
    simp only [M, G11, G12]
    rw [hEblocks, Matrix.fromBlocks_multiply, hBL, hBR]
  have hMtr : Matrix.transpose M =
      Matrix.fromBlocks E11 (Matrix.transpose B1) E21 (Matrix.transpose B2) := by
    simp only [M]
    rw [Matrix.fromBlocks_transpose]
    simp only [Matrix.transpose_transpose]
  have hzero : Matrix.transpose E11 * Matrix.transpose B1 +
      Matrix.transpose E21 * Matrix.transpose B2 = 0 := by
    have h := congrArg Matrix.transpose hBL
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_zero] at h
    exact h
  have hMM : M * Matrix.transpose M = Matrix.fromBlocks G11 0 0 (B * Matrix.transpose B) := by
    simp only [hMtr, M, G11]
    rw [Matrix.fromBlocks_multiply, hzero, hBL, ← hBB]
  have hG11 : G11 = (Matrix.transpose E * E).submatrix Sum.inl Sum.inl := by
    simp only [G11]
    rw [hEtr, hEblocks, Matrix.fromBlocks_multiply]
    rfl
  have hMMd : (M * Matrix.transpose M).det = G11.det * (B * Matrix.transpose B).det := by
    rw [hMM, Matrix.det_fromBlocks_zero₂₁]
  have hMEd : (M * E).det = G11.det * S.det := by
    rw [hME, Matrix.det_fromBlocks_zero₂₁]
  have hsq : (M * Matrix.transpose M).det = M.det ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose, sq]
  have key1 : G11.det * (B * Matrix.transpose B).det = M.det ^ 2 := by
    rw [← hMMd, hsq]
  have hMEmul : (M * E).det = M.det * E.det := Matrix.det_mul M E
  have key2 : G11.det * (B * Matrix.transpose B).det * E.det ^ 2 = (G11.det * S.det) ^ 2 := by
    rw [key1, ← mul_pow, ← hMEmul, hMEd]
  rw [hG11] at key2
  rw [mul_pow] at key2
  exact key2

/-- **Determinant bound for the kernel of a full-rank matrix.** Let `E` be an invertible `(k+n) x (k+n)` real matrix with `det E = ±1`, let `B` be an `n x (k+n)` real matrix and `S` an `n x n` real matrix such that `B * E` vanishes on the first `k` columns and equals `S` on the last `n` columns. Then the Gram determinant of the first `k` columns of `E` is at most the Gram determinant of the rows of `B`. Proof route (all Mathlib): put `G := Matrix.transpose E * E`, so `det G = (det E)^2 = 1`; writing `G` as a block matrix on `Fin k ⊕ Fin n` gives `Matrix.transpose C * C = G11` for `C := E.submatrix id Sum.inl`, and `B = [0 | S] * E⁻¹` (here `E` is invertible), whence `B * Matrix.transpose B = S * (G⁻¹)₂₂ * Matrix.transpose S`. The Schur complement identities `Matrix.det_fromBlocks₁₁` and `Matrix.invOf_fromBlocks₁₁_eq` give `det ((G⁻¹)₂₂) = det (G11) / det G = det (Matrix.transpose C * C)`, so `det (B * Matrix.transpose B) = (det S)^2 * det (Matrix.transpose C * C)`, and `1 ≤ |det S|` together with `0 ≤ det (Matrix.transpose C * C)` (Gram matrix of a real matrix, positive semidefinite) finishes. -/
theorem det_transpose_mul_le_of_kernel {k n : ℕ}
    (B : Matrix (Fin n) (Fin k ⊕ Fin n) ℝ)
    (E : Matrix (Fin k ⊕ Fin n) (Fin k ⊕ Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hE : E.det = 1 ∨ E.det = -1)
    (hBE : ∀ (l : Fin n) (a : Fin k ⊕ Fin n),
      (B * E) l a = Sum.elim (fun _ : Fin k => (0 : ℝ)) (fun j : Fin n => S l j) a)
    (hS : 1 ≤ |S.det|) :
    (Matrix.transpose (E.submatrix id Sum.inl) * (E.submatrix id Sum.inl)).det ≤
      (B * Matrix.transpose B).det := by
  have hC : Matrix.transpose (E.submatrix id Sum.inl) * (E.submatrix id Sum.inl) =
      (Matrix.transpose E * E).submatrix Sum.inl Sum.inl := rfl
  have hdetEsq : E.det ^ 2 = 1 := by rcases hE with h | h <;> rw [h] <;> norm_num
  have key3 : ((Matrix.transpose E * E).submatrix Sum.inl Sum.inl).det *
      (B * Matrix.transpose B).det =
      ((Matrix.transpose E * E).submatrix Sum.inl Sum.inl).det ^ 2 * S.det ^ 2 := by
    have h := det_transpose_mul_mul_sq B E S hBE
    rw [hdetEsq, mul_one] at h
    exact h
  have hGnn : 0 ≤ ((Matrix.transpose E * E).submatrix Sum.inl Sum.inl).det := by
    rw [← hC]
    have hpsd : (Matrix.transpose (E.submatrix id Sum.inl) * (E.submatrix id Sum.inl)).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_conjTranspose_mul_self (E.submatrix id Sum.inl)
    exact hpsd.det_nonneg
  have hBnn : 0 ≤ (B * Matrix.transpose B).det := by
    have hpsd : (B * Matrix.transpose B).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose B
    exact hpsd.det_nonneg
  have hS2 : 1 ≤ S.det ^ 2 := by
    nlinarith [abs_nonneg S.det, sq_abs S.det, hS]
  rw [hC]
  rcases eq_or_lt_of_le hGnn with h0 | hpos
  · rw [← h0]; exact hBnn
  · have hkey : (B * Matrix.transpose B).det =
        ((Matrix.transpose E * E).submatrix Sum.inl Sum.inl).det * S.det ^ 2 := by
      have h2 : ((Matrix.transpose E * E).submatrix Sum.inl Sum.inl).det *
            (B * Matrix.transpose B).det =
          ((Matrix.transpose E * E).submatrix Sum.inl Sum.inl).det *
            (((Matrix.transpose E * E).submatrix Sum.inl Sum.inl).det * S.det ^ 2) := by
        rw [key3]; ring
      exact mul_left_cancel₀ (ne_of_gt hpos) h2
    have h3 := mul_le_mul_of_nonneg_left hS2 (le_of_lt hpos)
    rw [mul_one] at h3
    linarith [hkey, h3]

end Commons.LinearAlgebra.Matrix