import Mathlib
import Submission.Commons.Analysis.Trace.trace_comp_ge_of_quadform_bounds

namespace Commons.Analysis.Trace

open scoped RealInnerProductSpace in
/-- For self-adjoint (symmetric) operators `C`, `N` on a finite-dimensional real inner product
space, if the quadratic form of `C` is bounded above by `c * ‖·‖ ^ 2` and `N` is positive
semi-definite, then `trace (C ∘ N) ≤ c * trace N`.

This is the mirror image of `trace_comp_ge_of_quadform_bounds`, obtained by applying that result
to `-C` with constant `-c`. -/
theorem trace_comp_le_of_quadform_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {C N : E →L[ℝ] E}
    (hC : C.IsSymmetric) (hN : N.IsSymmetric) {c : ℝ}
    (h1 : ∀ v : E, ⟪C v, v⟫ ≤ c * ‖v‖ ^ 2) (hNpos : ∀ v : E, 0 ≤ ⟪N v, v⟫) :
    LinearMap.trace ℝ E ((C : E →ₗ[ℝ] E) ∘ₗ (N : E →ₗ[ℝ] E))
      ≤ c * LinearMap.trace ℝ E (N : E →ₗ[ℝ] E) := by
  -- `-C` is symmetric with quadratic form bounded below by `-c * ‖·‖ ^ 2`.
  have hcoe : (((-C : E →L[ℝ] E)) : E →ₗ[ℝ] E) = -(C : E →ₗ[ℝ] E) := by simp
  have hneg : ((-C : E →L[ℝ] E)).IsSymmetric := by
    rw [hcoe]
    intro x y
    rw [LinearMap.neg_apply, LinearMap.neg_apply, inner_neg_left, inner_neg_right, hC x y]
  have hbound : ∀ v : E, (-c) * ‖v‖ ^ 2 ≤ ⟪(-C : E →L[ℝ] E) v, v⟫ := by
    intro v
    have h := h1 v
    rw [neg_apply, inner_neg_left]
    linarith
  -- Apply the lower bound to `-C`.
  have h := trace_comp_ge_of_quadform_bounds hneg hN hbound hNpos
  rw [hcoe] at h
  have hnegcomp : (-(C : E →ₗ[ℝ] E)) ∘ₗ (N : E →ₗ[ℝ] E)
      = -((C : E →ₗ[ℝ] E) ∘ₗ (N : E →ₗ[ℝ] E)) := by
    ext x; simp
  rw [hnegcomp, map_neg] at h
  linarith [h]

end Commons.Analysis.Trace
