import Mathlib.Analysis.InnerProductSpace.GramMatrix

namespace Commons.Analysis.InnerProductSpace

open Matrix

theorem gram_det_ne_zero_of_linearIndependent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} (h : LinearIndependent ℝ ![x, y]) :
    (Matrix.det ![![inner ℝ x x, inner ℝ x y], ![inner ℝ y x, inner ℝ y y]]) ≠ 0 := by
  -- The displayed 2 × 2 matrix is exactly the Gram matrix of the family ![x, y].
  have hEq : (Matrix.det ![![inner ℝ x x, inner ℝ x y], ![inner ℝ y x, inner ℝ y y]]) =
      (Matrix.gram ℝ (![x, y] : Fin 2 → E)).det := by
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hEq]
  -- A Gram matrix is nonsingular iff the underlying family is linearly independent.
  exact (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ) (v := (![x, y] : Fin 2 → E))).mpr h

end Commons.Analysis.InnerProductSpace