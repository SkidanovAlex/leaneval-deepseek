import Mathlib
import Submission.Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq
import Submission.Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues
import Submission.Commons.Analysis.Sigma2.trace_sq_eq_sum_eigenvalues_sq

namespace Commons.Analysis.Trace

open scoped InnerProductSpace
open scoped BigOperators

open scoped InnerProductSpace in
theorem sqrt_trace_adjoint_comp_le_trace_of_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {S : E →L[ℝ] E} (hS : S.IsSymmetric) (hpos : ∀ v : E, 0 ≤ ⟪S v, v⟫_ℝ) :
    Real.sqrt (LinearMap.trace ℝ E (S.toLinearMap.adjoint ∘ₗ S))
      ≤ LinearMap.trace ℝ E (S.toLinearMap) := by
  classical
  -- Eigenvalues of a positive symmetric operator are nonnegative.
  have hnonneg : ∀ i : Fin (Module.finrank ℝ E), 0 ≤ hS.eigenvalues rfl i := by
    intro i
    have h := hpos ((hS.eigenvectorBasis rfl) i)
    change 0 ≤ ⟪(S : E →ₗ[ℝ] E) ((hS.eigenvectorBasis rfl) i), (hS.eigenvectorBasis rfl) i⟫_ℝ at h
    rw [LinearMap.IsSymmetric.apply_eigenvectorBasis (T := (S : E →ₗ[ℝ] E)) hS rfl i,
      real_inner_smul_left, (hS.eigenvectorBasis rfl).inner_eq_ite i i, if_pos rfl, mul_one] at h
    exact h
  -- Spectral bridge: both traces become sums of eigenvalues.
  have htrace : LinearMap.trace ℝ E (S.toLinearMap.adjoint ∘ₗ S)
      = ∑ i : Fin (Module.finrank ℝ E), (hS.eigenvalues rfl i) ^ 2 := by
    rw [Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq hS,
      Commons.Analysis.Sigma2.trace_sq_eq_sum_eigenvalues_sq hS]
  have htraceS : LinearMap.trace ℝ E (S.toLinearMap)
      = ∑ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i :=
    Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues hS
  rw [htrace, htraceS]
  have hsum_nonneg : 0 ≤ ∑ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i :=
    Finset.sum_nonneg (fun i _ => hnonneg i)
  -- Sum of squares of nonnegative numbers is at most the square of their sum.
  have hsq : (∑ i : Fin (Module.finrank ℝ E), (hS.eigenvalues rfl i) ^ 2)
      ≤ (∑ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i) ^ 2 := by
    have hterm : ∀ i ∈ Finset.univ,
        (hS.eigenvalues rfl i) ^ 2
          ≤ hS.eigenvalues rfl i * (∑ j : Fin (Module.finrank ℝ E), hS.eigenvalues rfl j) := by
      intro i _
      have h1 : hS.eigenvalues rfl i ≤ ∑ j : Fin (Module.finrank ℝ E), hS.eigenvalues rfl j :=
        Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      nlinarith [hnonneg i, h1]
    calc
      (∑ i : Fin (Module.finrank ℝ E), (hS.eigenvalues rfl i) ^ 2)
          ≤ ∑ i : Fin (Module.finrank ℝ E),
              hS.eigenvalues rfl i * (∑ j : Fin (Module.finrank ℝ E), hS.eigenvalues rfl j) :=
            Finset.sum_le_sum hterm
      _ = (∑ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i)
            * (∑ j : Fin (Module.finrank ℝ E), hS.eigenvalues rfl j) := by
            rw [Finset.sum_mul]
      _ = (∑ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i) ^ 2 := by ring
  rw [← Real.sqrt_sq hsum_nonneg]
  exact Real.sqrt_le_sqrt hsq

end Commons.Analysis.Trace
