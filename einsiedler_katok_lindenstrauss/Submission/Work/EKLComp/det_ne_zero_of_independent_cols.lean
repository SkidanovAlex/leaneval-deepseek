import Mathlib

open Matrix

namespace Work.EKLComp

/-- If the columns of an integer `3 × 3` matrix are linearly independent over `ℝ`
(where the entries are viewed in `ℝ`), then its determinant is nonzero. -/
theorem det_ne_zero_of_independent_cols (M : Matrix (Fin 3) (Fin 3) ℤ)
    (h : LinearIndependent ℝ (fun j => (fun i => (M i j : ℝ)))) :
    M.det ≠ 0 := by
  intro hdet
  -- View `M` as a real matrix; its columns are still linearly independent.
  have hli : LinearIndependent ℝ (Matrix.col (M.map (Int.castRingHom ℝ))) := h
  -- Linear independence of the columns makes the matrix invertible, hence its
  -- determinant is a unit.
  have hunit : IsUnit (M.map (Int.castRingHom ℝ)).det := by
    rw [← isUnit_iff_isUnit_det]
    exact (linearIndependent_cols_iff_isUnit).mp hli
  have hne : (M.map (Int.castRingHom ℝ)).det ≠ 0 := isUnit_iff_ne_zero.mp hunit
  -- The determinant of the cast matrix is the cast of the determinant.
  have hcast : (M.map (Int.castRingHom ℝ)).det = (M.det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) M).symm
  rw [hcast, hdet] at hne
  exact hne (by norm_num)

end Work.EKLComp
