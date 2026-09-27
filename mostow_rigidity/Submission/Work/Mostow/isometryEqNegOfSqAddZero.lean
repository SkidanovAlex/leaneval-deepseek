import Mathlib

set_option linter.unusedVariables false

namespace Work.Mostow

/-- An isometry `T` of a real inner product space which satisfies `(T + 1)² = 0` on an invariant
subspace `W` (`T (T x + x) = -(T x + x)` for `x ∈ W`) is `-1` there. -/
theorem isometryEqNegOfSqAddZero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V ≃ₗᵢ[ℝ] V) (W : Submodule ℝ V) (hW : ∀ x ∈ W, T x ∈ W)
    (h : ∀ x ∈ W, T (T x + x) = -(T x + x)) : ∀ x ∈ W, T x = -x := by
  intro x hx
  -- From `T (T x + x) = -(T x + x)` and injectivity/invertibility of `T`, the vector
  -- `z = T x + x` is also inverted by `T⁻¹`: `T⁻¹ z = -z`.
  have hsymm : T.symm (T x + x) = -(T x + x) :=
    T.injective (by rw [T.apply_symm_apply, map_neg, h x hx, neg_neg])
  -- Using that the adjoint of an isometry is its inverse,
  -- `⟨T x, z⟩ = ⟨x, T⁻¹ z⟩ = ⟨x, -z⟩ = -⟨x, z⟩`.
  have hTx : inner ℝ (T x) (T x + x) = - inner ℝ x (T x + x) := by
    calc inner ℝ (T x) (T x + x)
        = inner ℝ (T x) (T (T.symm (T x + x))) := by rw [T.apply_symm_apply]
      _ = inner ℝ x (T.symm (T x + x)) := T.inner_map_map x _
      _ = inner ℝ x (-(T x + x)) := by rw [hsymm]
      _ = - inner ℝ x (T x + x) := inner_neg_right x _
  -- Hence `⟨z, z⟩ = ⟨T x, z⟩ + ⟨x, z⟩ = 0`, so `z = 0`.
  have hzz : inner ℝ (T x + x) (T x + x) = 0 := by
    rw [inner_add_left (T x) x (T x + x), hTx, neg_add_cancel]
  have hz : T x + x = 0 := inner_self_eq_zero.mp hzz
  exact eq_neg_of_add_eq_zero_left hz

end Work.Mostow
