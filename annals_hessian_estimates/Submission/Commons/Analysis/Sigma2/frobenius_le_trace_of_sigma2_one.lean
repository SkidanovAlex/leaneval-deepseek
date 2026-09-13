import Mathlib
import Submission.Commons.Analysis.Sigma2.frobenius_sq_eq_trace_sq_sub_two_sigma2

namespace Commons.Analysis.Sigma2

/-! For a self-adjoint continuous linear operator `T` with sigma_1 > 0 and sigma_2 (sum over pairs of eigenvalues) equal to 1: the Frobenius norm `Real.sqrt (trace (T.adjoint ∘ T))` is at most the trace `sum_i (eigenvalues)`.  This is the reduction "second-derivative (Frobenius) control follows from Laplacian (trace) control" used at the very end of the proof of the sigma-2 Hessian estimate.  Proof: Frobenius^2 = sigma_1^2 - 2*sigma_2 = sigma_1^2 - 2 ≤ sigma_1^2 with sigma_1 > 0, and Real.sqrt is monotone. -/
open scoped BigOperators in
theorem frobenius_le_trace_of_sigma2_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric)
    (hσ1 : 0 < ∑ i : Fin (Module.finrank ℝ E), hT.eigenvalues rfl i)
    (hσ2 : (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) = 1) :
    Real.sqrt (LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E).adjoint ∘ₗ (T : E →ₗ[ℝ] E))) ≤
      ∑ i : Fin (Module.finrank ℝ E), hT.eigenvalues rfl i := by
  classical
  let s := ∑ i : Fin (Module.finrank ℝ E), hT.eigenvalues rfl i
  let x := LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E).adjoint ∘ₗ (T : E →ₗ[ℝ] E))
  -- Frobenius^2 = sigma_1^2 - 2*sigma_2 = sigma_1^2 - 2 ≤ sigma_1^2
  have hF := frobenius_sq_eq_trace_sq_sub_two_sigma2 hT
  have hsq : (Real.sqrt x) ^ 2 ≤ s ^ 2 := by
    dsimp [x, s]
    rw [hF, hσ2]
    nlinarith
  -- square both sides (both nonnegative)
  have hle_abs : |Real.sqrt x| ≤ |s| := sq_le_sq.mp hsq
  simpa [x, s, abs_of_nonneg (Real.sqrt_nonneg x), abs_of_nonneg (le_of_lt hσ1)] using hle_abs

end Commons.Analysis.Sigma2
