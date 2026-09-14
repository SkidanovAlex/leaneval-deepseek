import Mathlib.Analysis.InnerProductSpace.Laplacian

namespace Commons.Analysis.Calculus.FDeriv

open scoped BigOperators in
theorem laplacian_eq_sum_second_partials {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) (u : E → ℝ)
    (x : E) :
    (Laplacian.laplacian u) x =
      ∑ i : ι, bilinearIteratedFDerivTwo ℝ u x (v i) (v i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u v]
  change (∑ i : ι, (iteratedFDeriv ℝ 2 u x) ![v i, v i]) =
    (∑ i : ι, ((bilinearIteratedFDerivTwo ℝ u x) (v i)) (v i))
  exact Finset.sum_congr rfl
    (fun i _hi => (bilinearIteratedFDerivTwo_eq_iteratedFDeriv u x (v i) (v i)).symm)

end Commons.Analysis.Calculus.FDeriv