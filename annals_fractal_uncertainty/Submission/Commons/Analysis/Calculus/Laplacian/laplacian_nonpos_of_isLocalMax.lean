import Mathlib.Analysis.InnerProductSpace.Laplacian
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonpos_of_localMax

namespace Commons.Analysis.Calculus.Laplacian

theorem laplacian_nonpos_of_isLocalMax {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) :
    Laplacian.laplacian f x ≤ 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)]
  apply Finset.sum_nonpos
  intro i _
  rw [iteratedFDeriv_two_apply]
  exact Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonpos_of_localMax hf hmax
    ((stdOrthonormalBasis ℝ E) i)

end Commons.Analysis.Calculus.Laplacian