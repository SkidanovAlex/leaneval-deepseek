import Mathlib

namespace Work.L2F.Props

/-- In `2 × 2` matrices over a commutative ring, two traceless matrices `X`, `Y` satisfy
`X * Y + Y * X = (X * Y).trace • 1`. -/
theorem traceless_mul_add_mul_trace (F : Type*) [CommRing F]
    (X Y : Matrix (Fin 2) (Fin 2) F) (hX : X.trace = 0) (hY : Y.trace = 0) :
    X * Y + Y * X = (X * Y).trace • 1 := by
  -- `hX : X.trace = 0` unfolds (for `Fin 2`) to `X 0 0 + X 1 1 = 0`, hence `X 1 1 = -X 0 0`.
  have hX11 : X 1 1 = - X 0 0 := by
    have h : X 0 0 + X 1 1 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using hX
    linear_combination h
  have hY11 : Y 1 1 = - Y 0 0 := by
    have h : Y 0 0 + Y 1 1 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using hY
    linear_combination h
  -- Reduce to the four entries and check each coordinate identity by `ring`.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.mul_apply, Matrix.trace, Matrix.smul_apply,
      Fin.sum_univ_two, hX11, hY11] <;> ring

end Work.L2F.Props
