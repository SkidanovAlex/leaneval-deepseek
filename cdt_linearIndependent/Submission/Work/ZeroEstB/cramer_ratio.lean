import Mathlib

/-!
# Cramer's rule in the form `(P.submatrix id I)⁻¹ * P = det(·)/det`

For a field `K`, a matrix `P : Matrix (Fin r) (Fin m) K`, and a choice of rows
`I : Fin r → Fin m` with `A := P.submatrix id I` invertible, the `(i,j)` entry of
`A⁻¹ * P` is the ratio of the determinant of `A` with the `i`-th column replaced by
the `j`-th column of `P` to `det A`.

This is Cramer's rule (`Matrix.det_smul_inv_mulVec_eq_cramer`) applied to the `j`-th
column of `P`, together with the observation that replacing the `i`-th column of
`P.submatrix id I` by the `j`-th column of `P` is exactly
`P.submatrix id (Function.update I i j)`.
-/

namespace Work.ZeroEstB

theorem cramer_ratio {K : Type*} [Field K] {r m : ℕ} (P : Matrix (Fin r) (Fin m) K)
    (I : Fin r → Fin m) (hd : (P.submatrix id I).det ≠ 0) (i : Fin r) (j : Fin m) :
    ((P.submatrix id I)⁻¹ * P) i j =
      (P.submatrix id (Function.update I i j)).det / (P.submatrix id I).det := by
  -- The determinant of `A := P.submatrix id I` with its `i`-th column replaced by the
  -- `j`-th column of `P` is `P.submatrix id (Function.update I i j)`.
  have hc : (P.submatrix id I).updateCol i (fun k => P k j)
      = P.submatrix id (Function.update I i j) := by
    ext k l
    by_cases hli : l = i
    · subst hli; simp [Matrix.updateCol]
    · simp [Matrix.updateCol, hli]
  -- Cramer's rule for the column `b k = P k j`.
  have key : (P.submatrix id I).det * ((P.submatrix id I)⁻¹ * P) i j
      = (P.submatrix id (Function.update I i j)).det := by
    have h1 := congr_fun (Matrix.det_smul_inv_mulVec_eq_cramer (P.submatrix id I) (fun k => P k j)
      (isUnit_iff_ne_zero.mpr hd)) i
    rw [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply] at h1
    rw [hc] at h1
    rw [← h1]
    congr 1
  rw [eq_div_iff hd, mul_comm]
  exact key

end Work.ZeroEstB
