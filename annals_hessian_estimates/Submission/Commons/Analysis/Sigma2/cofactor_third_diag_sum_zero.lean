import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.first_deriv_sigma2_coord
import Submission.Commons.Analysis.Sigma2.diagonal_first_deriv_sigma2

namespace Commons.Analysis.Sigma2

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem cofactor_third_diag_sum_zero {u : EuclideanSpace ℝ (Fin 4) → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin 4))} {x : EuclideanSpace ℝ (Fin 4)}
    {v : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4))}
    (hs : IsOpen s) (hu : ContDiffOn ℝ 3 u s) (hx : x ∈ s)
    (hconst : ∀ y ∈ s, (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (iteratedFDeriv ℝ 2 u y) ![v i, v i] * (iteratedFDeriv ℝ 2 u y) ![v j, v j] -
          ((iteratedFDeriv ℝ 2 u y) ![v i, v j]) ^ 2 else 0) = 1)
    {lam : Fin 4 → ℝ}
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0)
    (k : Fin 4) :
    (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
      * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]) = 0 := by
  refine diagonal_first_deriv_sigma2 lam
    (fun i j => (iteratedFDeriv ℝ 2 u x) ![v i, v j])
    (fun k i j => (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j])
    k hdiag ?_
  exact Commons.Analysis.Calculus.FDeriv.first_deriv_sigma2_coord hs hu hx hconst k

end Commons.Analysis.Sigma2
