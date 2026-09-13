import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Commons.LinearAlgebra.Matrix

theorem map_ker_mulVecLin {R : Type*} [CommSemiring R] {l m : Type*} [Fintype m]
    (M : Matrix l m R) :
    Submodule.map M.mulVecLin (LinearMap.ker M.mulVecLin) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro _ ⟨y, hy, rfl⟩
  simpa using hy

end Commons.LinearAlgebra.Matrix