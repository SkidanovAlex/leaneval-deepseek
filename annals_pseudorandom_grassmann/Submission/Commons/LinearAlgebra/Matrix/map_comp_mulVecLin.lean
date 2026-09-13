import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Commons.LinearAlgebra.Matrix

theorem map_comp_mulVecLin {R : Type*} [CommSemiring R] {l m n : Type*}
    [Fintype m] [Fintype n] (M : Matrix l m R) (N : Matrix m n R)
    (S : Submodule R (n → R)) :
    Submodule.map (M.mulVecLin ∘ₗ N.mulVecLin) S
      = Submodule.map M.mulVecLin (Submodule.map N.mulVecLin S) := by
  exact Submodule.map_comp N.mulVecLin M.mulVecLin S

end Commons.LinearAlgebra.Matrix