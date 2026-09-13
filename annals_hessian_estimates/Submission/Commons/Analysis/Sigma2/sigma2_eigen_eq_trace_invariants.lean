import Mathlib
import Submission.Commons.Analysis.Sigma2.pairSum_sq
import Submission.Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues
import Submission.Commons.Analysis.Sigma2.trace_sq_eq_sum_eigenvalues_sq

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem sigma2_eigen_eq_trace_invariants {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric) :
    (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) =
      ((LinearMap.trace ℝ E (T : E →ₗ[ℝ] E)) ^ 2
        - LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E))) / 2 := by
  classical
  have hpair := pairSum_sq (a := fun i => hT.eigenvalues rfl i)
  have htr := trace_eq_sum_eigenvalues hT
  have htr2 := trace_sq_eq_sum_eigenvalues_sq hT
  rw [htr, htr2]
  linarith [hpair]

end Commons.Analysis.Sigma2
