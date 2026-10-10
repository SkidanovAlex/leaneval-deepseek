import Mathlib
import Submission.Work.TwistModel.Pfaffian
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The adjugate of a `5 × 5` alternating matrix

For a `5 × 5` matrix `A` over a commutative ring which is skew-symmetric (`Aᵀ = -A`) with vanishing
diagonal, the adjugate is the outer product of the five Pfaffians:

  `A.adjugate i j = (-1) ^ (i + j) * pᵢ * pⱼ`,  `pᵢ = Matrix.skewPfaffian5 A i`.

This is the classical identity of [SZ] §2 (Buchsbaum–Eisenbud); Mathlib carries the general
cofactor expansion `Matrix.adjugate_fin_succ_eq_det_submatrix`
(`adjugate A i j = (-1)^(i+j) * det (A.submatrix j.succAbove i.succAbove)`), so it remains to
identify the four by four minor deleting row `j` and column `i` with `pᵢ * pⱼ`
(`det_submatrix_eq_skewPfaffian5_mul`).  Both sides being polynomials of degree `4` in the ten
independent entries of `A`, the identification is a polynomial identity which is proved here by
expanding along a row and using `ring`.
-/

set_option autoImplicit false

namespace Work.TwistModel

/-- Expansion of the determinant of a `4 × 4` matrix along its first row: the `24` signed
monomials, with each `3 × 3` minor expanded by `Matrix.det_fin_three`. -/
lemma det_fin_four_expand {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det = M 0 0 * M 1 1 * M 2 2 * M 3 3 - M 0 0 * M 1 1 * M 2 3 * M 3 2
      - M 0 0 * M 1 2 * M 2 1 * M 3 3 + M 0 0 * M 1 2 * M 2 3 * M 3 1
      + M 0 0 * M 1 3 * M 2 1 * M 3 2 - M 0 0 * M 1 3 * M 2 2 * M 3 1
      - M 0 1 * M 1 0 * M 2 2 * M 3 3 + M 0 1 * M 1 0 * M 2 3 * M 3 2
      + M 0 1 * M 1 2 * M 2 0 * M 3 3 - M 0 1 * M 1 2 * M 2 3 * M 3 0
      - M 0 1 * M 1 3 * M 2 0 * M 3 2 + M 0 1 * M 1 3 * M 2 2 * M 3 0
      + M 0 2 * M 1 0 * M 2 1 * M 3 3 - M 0 2 * M 1 0 * M 2 3 * M 3 1
      - M 0 2 * M 1 1 * M 2 0 * M 3 3 + M 0 2 * M 1 1 * M 2 3 * M 3 0
      + M 0 2 * M 1 3 * M 2 0 * M 3 1 - M 0 2 * M 1 3 * M 2 1 * M 3 0
      - M 0 3 * M 1 0 * M 2 1 * M 3 2 + M 0 3 * M 1 0 * M 2 2 * M 3 1
      + M 0 3 * M 1 1 * M 2 0 * M 3 2 - M 0 3 * M 1 1 * M 2 2 * M 3 0
      - M 0 3 * M 1 2 * M 2 0 * M 3 1 + M 0 3 * M 1 2 * M 2 1 * M 3 0 := by
  rw [Matrix.det_succ_row _ 0]
  simp only [Fin.sum_univ_four]
  simp [Matrix.det_fin_three, Fin.succAbove]
  first | refl_ring1 | ring

/-- **Every `4 × 4` minor of a `5 × 5` alternating matrix is a product of two Pfaffians**: the
determinant of `A` with row `j` and column `i` deleted equals `pᵢ * pⱼ`.

This is a polynomial identity of degree `4` in the ten independent entries of `A` (the entries
above the diagonal); after substituting the skew-symmetric normal form the two sides agree by
`ring`. -/
lemma det_submatrix_eq_skewPfaffian5_mul {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R)
    (hskew : Matrix.transpose A = -A) (hdiag : ∀ i : Fin 5, A i i = 0) (i j : Fin 5) :
    (A.submatrix j.succAbove i.succAbove).det =
      Matrix.skewPfaffian5 A i * Matrix.skewPfaffian5 A j := by
  have hskew' : ∀ i j : Fin 5, A j i = - A i j := by
    intro i j
    have h := congrFun (congrFun hskew i) j
    simpa using h
  -- a skew-symmetric matrix with vanishing diagonal is determined by its entries above the diagonal
  have hA : A = !![0, A 0 1, A 0 2, A 0 3, A 0 4;
      -A 0 1, 0, A 1 2, A 1 3, A 1 4;
      -A 0 2, -A 1 2, 0, A 2 3, A 2 4;
      -A 0 3, -A 1 3, -A 2 3, 0, A 3 4;
      -A 0 4, -A 1 4, -A 2 4, -A 3 4, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [hdiag 0, hdiag 1, hdiag 2, hdiag 3, hdiag 4,
        hskew' 0 1, hskew' 0 2, hskew' 0 3, hskew' 0 4,
        hskew' 1 2, hskew' 1 3, hskew' 1 4, hskew' 2 3, hskew' 2 4, hskew' 3 4]
  rw [hA]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.skewPfaffian5, Matrix.pfaffian4, det_fin_four_expand, Fin.succAbove] <;> ring

/-- The adjugate of a `5 × 5` alternating matrix is `(-1)^{i+j} pᵢ pⱼ` in the Pfaffians of the
principal `4 × 4` minors. -/
theorem adjugate_eq_skewPfaffian5 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R)
    (hskew : Matrix.transpose A = -A) (hdiag : ∀ i : Fin 5, A i i = 0) (i j : Fin 5) :
    A.adjugate i j = (-1 : R) ^ ((i : ℕ) + (j : ℕ)) *
      Matrix.skewPfaffian5 A i * Matrix.skewPfaffian5 A j := by
  calc A.adjugate i j
      = (-1 : R) ^ ((j : ℕ) + (i : ℕ)) * (A.submatrix j.succAbove i.succAbove).det :=
        Matrix.adjugate_fin_succ_eq_det_submatrix A i j
    _ = (-1 : R) ^ ((i : ℕ) + (j : ℕ)) * (A.submatrix j.succAbove i.succAbove).det := by
        rw [add_comm]
    _ = (-1 : R) ^ ((i : ℕ) + (j : ℕ)) *
          (Matrix.skewPfaffian5 A i * Matrix.skewPfaffian5 A j) := by
        rw [det_submatrix_eq_skewPfaffian5_mul A hskew hdiag i j]
    _ = (-1 : R) ^ ((i : ℕ) + (j : ℕ)) * Matrix.skewPfaffian5 A i *
          Matrix.skewPfaffian5 A j := by
        rw [mul_assoc]

end Work.TwistModel
