import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Submission.Commons.LinearAlgebra.Matrix.linearIndependent_rat_of_int

namespace Commons.LinearAlgebra.Matrix

/-- A square integer matrix whose columns are linearly independent over `ℤ`
has nonzero determinant.

The columns remain linearly independent after the embedding `ℤ ↪ ℚ`; a square
matrix over the field `ℚ` with linearly independent columns is a unit, hence has
nonzero determinant; the integer determinant is nonzero because it maps to the
nonzero rational determinant under the (injective) casting `ℤ ↪ ℚ`. -/
theorem det_ne_zero_of_cols_linearIndependent {r : ℕ} (U : Matrix (Fin r) (Fin r) ℤ)
    (h : LinearIndependent ℤ U.col) : U.det ≠ 0 := by
  classical
  let V : Matrix (Fin r) (Fin r) ℚ := U.map (fun z : ℤ => (z : ℚ))
  -- Linearly independent columns over `ℤ` stay linearly independent over `ℚ`.
  have hb : LinearIndependent ℚ
      (fun j : Fin r => fun i : Fin r => ((U i j : ℤ) : ℚ)) := by
    exact linearIndependent_rat_of_int (w := fun j : Fin r => fun i : Fin r => U i j)
      (by
        have hcolU : (fun j : Fin r => fun i : Fin r => U i j) = U.col := by
          ext j i
          rfl
        rw [hcolU]
        exact h)
  have hVcol : V.col = fun j : Fin r => fun i : Fin r => ((U i j : ℤ) : ℚ) := by
    ext j i
    simp [V, Matrix.col_apply]
  have hV : LinearIndependent ℚ V.col := by
    simpa [hVcol] using hb
  -- A square matrix over a field with linearly independent columns is a unit,
  -- so its determinant is a unit and therefore nonzero.
  have hVunit : IsUnit V := (Matrix.linearIndependent_cols_iff_isUnit (A := V)).mp hV
  have hVdetUnit : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hVunit
  have hVdet_ne : V.det ≠ 0 := (isUnit_iff_ne_zero.mp hVdetUnit)
  -- The rational determinant is the cast of the integer determinant.
  have hcast : (U.det : ℚ) = V.det := by
    simpa [V] using (Int.cast_det (R := ℚ) U)
  intro hUdet
  apply hVdet_ne
  rw [← hcast]
  exact_mod_cast hUdet

end Commons.LinearAlgebra.Matrix