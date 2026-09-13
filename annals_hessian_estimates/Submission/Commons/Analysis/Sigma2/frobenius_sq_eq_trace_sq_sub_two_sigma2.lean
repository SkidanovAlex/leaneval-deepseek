import Mathlib
import Submission.Commons.Analysis.Sigma2.pairSum_sq
import Submission.Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq
import Submission.Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues
import Submission.Commons.Analysis.Sigma2.trace_sq_eq_sum_eigenvalues_sq

namespace Commons.Analysis.Sigma2

/-! For a self-adjoint continuous linear operator `T` on a finite-dimensional real inner product space: `(Frobenius norm of T)^2 = (trace T)^2 - 2 * sigma_2(eigenvalues of T)`, where the Frobenius norm is `Real.sqrt (trace (T.adjoint ∘ T))` and sigma_2 is the sum over pairs `i < j` of products of the eigenvalues `hT.eigenvalues rfl`.  Compose: trace(adjoint ∘ T) = trace(T ∘ T) = sum of squares of eigenvalues, and `(sum of eigenvalues)^2 = sum of squares + 2 * sigma_2`. -/
open scoped BigOperators in
theorem frobenius_sq_eq_trace_sq_sub_two_sigma2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric) :
    (Real.sqrt (LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E).adjoint ∘ₗ (T : E →ₗ[ℝ] E)))) ^ 2 =
      (∑ i : Fin (Module.finrank ℝ E), hT.eigenvalues rfl i) ^ 2 -
        2 * (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) := by
  classical
  have hnonneg : 0 ≤ LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E).adjoint ∘ₗ (T : E →ₗ[ℝ] E)) := by
    rw [trace_adjoint_sq_eq_trace_sq hT]
    rw [trace_sq_eq_sum_eigenvalues_sq hT]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (hT.eigenvalues rfl i))
  rw [Real.sq_sqrt hnonneg]
  rw [trace_adjoint_sq_eq_trace_sq hT]
  rw [trace_sq_eq_sum_eigenvalues_sq hT]
  have hpair := pairSum_sq (a := hT.eigenvalues rfl)
  nlinarith

end Commons.Analysis.Sigma2
