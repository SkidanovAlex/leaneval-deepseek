import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Sigma2.sigma1_sq_ge_two
import Submission.Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem trace_sq_ge_two_of_pair_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric)
    (hpair : (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) = 1) :
    2 ≤ (LinearMap.trace ℝ E (T : E →ₗ[ℝ] E)) ^ 2 := by
  rw [trace_eq_sum_eigenvalues hT]
  have hsq := pairSum_sq (a := hT.eigenvalues rfl)
  rw [hpair] at hsq
  have hnonneg : 0 ≤ ∑ i : Fin (Module.finrank ℝ E), (hT.eigenvalues rfl i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [hsq, hnonneg]

end Commons.Analysis.Sigma2