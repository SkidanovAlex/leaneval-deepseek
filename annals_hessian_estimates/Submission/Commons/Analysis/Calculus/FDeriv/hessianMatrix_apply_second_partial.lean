import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
theorem hessianMatrix_apply_second_partial {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) (u : E → ℝ)
    (x : E) (i j : ι) :
    ⟪(InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ u) x)) (v i), v j⟫ =
      bilinearIteratedFDerivTwo ℝ u x (v i) (v j) := by
  -- `continuousLinearMapOfBilin` is the Fréchet–Riesz representative: its value at a point
  -- paired with a vector equals the original (bi)linear form applied to the two vectors.
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
  -- `bilinearIteratedFDerivTwo` is literally the second iterated derivative applied to the
  -- two vectors, i.e. `fderiv (fderiv u) x` applied to them.
  rfl

end Commons.Analysis.Calculus.FDeriv