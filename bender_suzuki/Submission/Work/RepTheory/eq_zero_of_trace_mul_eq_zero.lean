import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.RepTheory

/-- If a linear endomorphism `B` of a finite-dimensional complex vector space is
orthogonal to every endomorphism with respect to the trace pairing
`(X, Y) ↦ trace (X * Y)`, then `B = 0`.

This is the non-degeneracy of the trace pairing on `End V`: choose a basis,
transport the hypothesis to matrices, where `trace (x * M) = 0` for all `x`
forces `M = 0` (take `x` to be a matrix unit). -/
theorem eq_zero_of_trace_mul_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {B : V →ₗ[ℂ] V}
    (h : ∀ X : V →ₗ[ℂ] V, LinearMap.trace ℂ V (X * B) = 0) : B = 0 := by
  classical
  let b := Module.finBasis ℂ V
  -- The matrix of `B` is orthogonal, w.r.t. the trace pairing, to every matrix.
  have hM : ∀ x : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ,
      (x * LinearMap.toMatrix b b B).trace = 0 := by
    intro x
    have hx : x = LinearMap.toMatrix b b (Matrix.toLin b b x) :=
      (LinearMap.toMatrix_toLin b b x).symm
    rw [hx, ← LinearMap.toMatrix_mul, ← LinearMap.trace_eq_matrix_trace ℂ b]
    exact h _
  -- Non-degeneracy of the trace pairing on matrices yields `toMatrix b b B = 0`.
  have hzero : LinearMap.toMatrix b b B = 0 := by
    rw [Matrix.ext_iff_trace_mul_left]
    intro x
    rw [hM x]
    simp
  -- Finally, `toMatrix b b` is injective.
  exact (LinearMap.toMatrix b b).injective (by simp [hzero])

end Work.RepTheory
