import Mathlib

open scoped Matrix

namespace Work.L2F.Props.oddsub

/-- The two eigenvalues of a `2 × 2` matrix over a field with a basis of eigenvectors multiply to
the determinant; and if the determinant is `1` and one eigenvalue is `1`, the matrix is the
identity. -/
theorem eigenbasis_mul_eq_det_and_eq_one {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K)
    (v w : Fin 2 → K) (hind : LinearIndependent K ![v, w])
    (lam mu : K) (hv : Matrix.mulVec M v = lam • v) (hw : Matrix.mulVec M w = mu • w) :
    lam * mu = M.det ∧ (M.det = 1 → lam = 1 → M = 1) := by
  -- `P` is the matrix with rows `v`, `w`; `Q = Pᵀ` is the matrix with columns `v`, `w`;
  -- `D` is the diagonal matrix with entries `lam`, `mu`.
  set P : Matrix (Fin 2) (Fin 2) K := Matrix.of (![v, w] : Fin 2 → Fin 2 → K) with hPdef
  set Q : Matrix (Fin 2) (Fin 2) K := Matrix.transpose P with hQdef
  set D : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![lam, mu] with hDdef
  -- `P` is invertible, hence so is `Q` (and their determinants are nonzero).
  have hPdet : IsUnit P.det :=
    (Matrix.isUnit_iff_isUnit_det P).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp (by rw [hPdef, Matrix.of_row]; exact hind))
  have hQdet : IsUnit Q.det := by rw [hQdef, Matrix.det_transpose]; exact hPdet
  have hQdetnz : Q.det ≠ 0 := hQdet.ne_zero
  -- The columns of `Q` are `v` and `w`.
  have hQcol : Q.col = (![v, w] : Fin 2 → Fin 2 → K) := by
    rw [hQdef, hPdef]; exact Matrix.of_col (![v, w] : Fin 2 → Fin 2 → K)
  have hQ0 : Q.col 0 = v := by rw [hQcol]; rfl
  have hQ1 : Q.col 1 = w := by rw [hQcol]; simp
  -- The columns of `D` are `lam • e₀` and `mu • e₁`.
  have hDc0 : D.col 0 = lam • Pi.single 0 1 := by
    rw [hDdef]; ext i; fin_cases i <;> simp [Matrix.col_apply]
  have hDc1 : D.col 1 = mu • Pi.single 1 1 := by
    rw [hDdef]; ext i; fin_cases i <;> simp [Matrix.col_apply]
  -- The two columns of `M * Q` and `Q * D` agree.
  have hcol0 : (M * Q).col 0 = (Q * D).col 0 := by
    rw [Matrix.col_mul_eq_mulVec_col, Matrix.col_mul_eq_mulVec_col, hQ0, hv, hDc0,
      Matrix.mulVec_smul, Matrix.mulVec_single_one, hQ0]
  have hcol1 : (M * Q).col 1 = (Q * D).col 1 := by
    rw [Matrix.col_mul_eq_mulVec_col, Matrix.col_mul_eq_mulVec_col, hQ1, hw, hDc1,
      Matrix.mulVec_smul, Matrix.mulVec_single_one, hQ1]
  have hMQ : M * Q = Q * D := by
    ext i j
    fin_cases j
    · exact congrFun hcol0 i
    · exact congrFun hcol1 i
  -- Taking determinants gives `M.det * Q.det = Q.det * (lam * mu)`, and `Q.det ≠ 0`.
  have hDdet : D.det = lam * mu := by
    rw [hDdef, Matrix.det_diagonal, Fin.prod_univ_two]; simp
  have hdet : lam * mu = M.det := by
    have h := congrArg Matrix.det hMQ
    rw [Matrix.det_mul, Matrix.det_mul, hDdet] at h
    have h2 : Q.det * M.det = Q.det * (lam * mu) := by rw [mul_comm Q.det M.det]; exact h
    exact (mul_left_cancel₀ hQdetnz h2).symm
  refine ⟨hdet, ?_⟩
  -- If `M.det = 1` and `lam = 1`, then `mu = 1`, so `D = 1`, hence `M * Q = Q` and `M = 1`.
  intro hdet1 hlam
  have hmu : mu = 1 := by
    have h := hdet
    rw [hdet1, hlam, one_mul] at h
    exact h
  have hD : D = 1 := by
    rw [hDdef]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hlam, hmu]
  have hMQ' : M * Q = Q := by rw [hMQ, hD, Matrix.mul_one]
  have hmc : M * Q = 1 * Q := by rw [hMQ', Matrix.one_mul]
  exact IsUnit.mul_right_cancel ((Matrix.isUnit_iff_isUnit_det Q).mpr hQdet) hmc

end Work.L2F.Props.oddsub
