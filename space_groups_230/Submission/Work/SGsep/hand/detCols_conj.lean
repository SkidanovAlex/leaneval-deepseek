import Mathlib
import Submission.Work.SGsep.hand.HandDefs2

/-!
# Naturality of the orientation determinant `detCols` under conjugation

`detCols u v w` is the determinant of the matrix whose *columns* are `u`, `v`, `w`.  Two elementary
linear-algebra facts drive the result:

* `detCols_mulVec` — `detCols` is multiplicative: applying a matrix `M` to all three columns
  multiplies the determinant by `det M`;
* `toRMat_det` — the real matrix `toRMat U` obtained from an integer matrix `U` has determinant
  the cast of `U.det` (`RingHom.map_det` for `Int.castRingHom ℝ`).

The main theorem `detCols_conj` is then immediate: from `B U = U A` one gets `B (U u) = U (A u)`
and `c' = U c`, so all three columns of the left-hand determinant are the images under `U` of the
three columns `u`, `A u`, `c` of the right-hand one.
-/

namespace Work.SGsep.hand

open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-- The matrix with rows `u`, `v`, `w`, conjugated by `M`, has as its columns the images of the
three columns of `Mᵀ`-conjugate: precisely, `[M u, M v, M w]ᵀ = M * [u v w]ᵀ`. -/
theorem of_transpose_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (u v w : Fin 3 → ℝ) :
    (Matrix.of ![M.mulVec u, M.mulVec v, M.mulVec w]).transpose
      = M * (Matrix.of ![u, v, w]).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply,
      Matrix.transpose_apply]

/-- `detCols` is multiplicative: applying a matrix to each of the three columns scales the
determinant by `det` of that matrix. -/
theorem detCols_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (u v w : Fin 3 → ℝ) :
    detCols (M.mulVec u) (M.mulVec v) (M.mulVec w) = M.det * detCols u v w := by
  unfold detCols
  rw [of_transpose_mulVec, Matrix.det_mul]

/-- The determinant of the real image of an integer matrix is the cast of its integer
determinant. -/
theorem toRMat_det (U : IMat) : (toRMat U).det = (U.det : ℝ) := by
  simpa [toRMat] using (RingHom.map_det (Int.castRingHom ℝ) U).symm

/-- The orientation determinant of a certificate is natural under conjugation: if `B U = U A` (as
real matrices) and `c' = U c`, then `det(y, B y, c') = det U · det(U⁻¹ y, A (U⁻¹ y), c)` — stated
with `y = U u`. -/
theorem detCols_conj {U A B : IMat} (hU : IsUnit U.det)
    (hB : (toRMat B) * (toRMat U) = (toRMat U) * (toRMat A))
    {c c' u : Fin 3 → ℝ} (hc : c' = (toRMat U).mulVec c) :
    detCols ((toRMat U).mulVec u) ((toRMat B).mulVec ((toRMat U).mulVec u)) c'
      = (U.det : ℝ) * detCols u ((toRMat A).mulVec u) c := by
  have _hU : IsUnit U.det := hU
  subst hc
  -- `B (U u) = U (A u)` because `B U = U A`
  have hBU : (toRMat B).mulVec ((toRMat U).mulVec u)
      = (toRMat U).mulVec ((toRMat A).mulVec u) := by
    simp only [Matrix.mulVec_mulVec, hB]
  rw [hBU, detCols_mulVec, toRMat_det]

end Work.SGsep.hand
