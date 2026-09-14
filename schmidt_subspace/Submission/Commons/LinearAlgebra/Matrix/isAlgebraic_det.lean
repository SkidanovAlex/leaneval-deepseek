import Mathlib.RingTheory.Algebraic.Integral

namespace Commons.LinearAlgebra.Matrix

theorem isAlgebraic_det {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) (h : ∀ i j, IsAlgebraic K (M i j)) :
    IsAlgebraic K M.det := by
  rw [isAlgebraic_iff_isIntegral, Matrix.det_apply']
  refine IsIntegral.sum _ fun σ _ => ?_
  refine IsIntegral.mul (isIntegral_intCast (R := K) (↑(Equiv.Perm.sign σ) : ℤ)) ?_
  exact IsIntegral.prod _ fun i _ => (h (σ i) i).isIntegral

end Commons.LinearAlgebra.Matrix