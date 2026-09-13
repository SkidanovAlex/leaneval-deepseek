import Submission.Commons.Analysis.Sigma2.sigma2_eigen_eq_trace_invariants

namespace Commons.Analysis.Sigma2

/-- If the pair sum `∑_{i<j} λᵢλⱼ` of the eigenvalues of a symmetric operator `T` equals `1`,
then `(tr T)² = 2 + tr (T ∘ T)`.

This is the identity `(∑ λᵢ)² = ∑ λᵢ² + 2 ∑_{i<j} λᵢλⱼ` combined with
`tr T = ∑ λᵢ` and `tr (T ∘ T) = ∑ λᵢ²`. -/
theorem trace_sq_eq_two_add_trace_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric)
    (hpair : (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) = 1) :
    (LinearMap.trace ℝ E (T : E →ₗ[ℝ] E)) ^ 2
      = 2 + LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E)) := by
  have h := sigma2_eigen_eq_trace_invariants hT
  rw [hpair] at h
  linarith

end Commons.Analysis.Sigma2
