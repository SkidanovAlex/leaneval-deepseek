import Mathlib.Analysis.InnerProductSpace.Trace

namespace Commons.Analysis.Trace

/- Cauchy–Schwarz inequality for the Hilbert–Schmidt inner product on endomorphisms of a
finite-dimensional real inner product space: for the pairing `⟨T, S⟩ = trace (T† ∘ S)` one has
`trace (T† ∘ S) ≤ √(trace (T† ∘ T)) * √(trace (S† ∘ S))`.

Here `T†` denotes the (linear-map) adjoint of `T`. The proof evaluates the traces in an
orthonormal basis `v` of `E`, using `trace (T† ∘ S) = ∑ i, ⟪T (v i), S (v i)⟫` and
`trace (T† ∘ T) = ∑ i, ‖T (v i)‖ ^ 2`, and then applies the elementary finite-sum
Cauchy–Schwarz inequality. -/
open scoped InnerProductSpace in
theorem trace_adjoint_comp_le_norm_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {T S : E →L[ℝ] E} :
    LinearMap.trace ℝ E (T.toLinearMap.adjoint ∘ₗ S)
      ≤ Real.sqrt (LinearMap.trace ℝ E (T.toLinearMap.adjoint ∘ₗ T))
        * Real.sqrt (LinearMap.trace ℝ E (S.toLinearMap.adjoint ∘ₗ S)) := by
  classical
  -- An orthonormal basis of `E`, indexed by `Fin (finrank ℝ E)`.
  let v : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  -- The left-hand side is the pairing `∑ i, ⟪T (v i), S (v i)⟫`.
  have h1 : LinearMap.trace ℝ E (T.toLinearMap.adjoint ∘ₗ S.toLinearMap)
      = ∑ i, inner ℝ (T (v i)) (S (v i)) := by
    rw [LinearMap.trace_eq_sum_inner _ v]
    apply Finset.sum_congr rfl
    intro i _
    simp only [LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_right]
    rfl
  -- Similarly `trace (T† ∘ T) = ∑ i, ‖T (v i)‖ ^ 2`.
  have h2 : LinearMap.trace ℝ E (T.toLinearMap.adjoint ∘ₗ T.toLinearMap)
      = ∑ i, ‖T (v i)‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner _ v]
    apply Finset.sum_congr rfl
    intro i _
    simp only [LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    rfl
  have h3 : LinearMap.trace ℝ E (S.toLinearMap.adjoint ∘ₗ S.toLinearMap)
      = ∑ i, ‖S (v i)‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner _ v]
    apply Finset.sum_congr rfl
    intro i _
    simp only [LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    rfl
  rw [h1, h2, h3]
  -- Cauchy–Schwarz: termwise bound, then the finite-sum form.
  refine le_trans (Finset.sum_le_sum (fun i _ => real_inner_le_norm _ _)) ?_
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ)
    (fun i => ‖T (v i)‖) (fun i => ‖S (v i)‖)
  simpa using hcs

end Commons.Analysis.Trace