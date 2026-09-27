import Mathlib

namespace Work.Mostow

/-- An isometry `T` of a real inner product space which satisfies `(T - 1)² = 0` on an invariant
subspace `W` (`T (T x - x) = T x - x` for `x ∈ W`) is the identity there. -/
theorem isometryEqOfSqSubZero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V ≃ₗᵢ[ℝ] V) (W : Submodule ℝ V) (hW : ∀ x ∈ W, T x ∈ W)
    (h : ∀ x ∈ W, T (T x - x) = T x - x) : ∀ x ∈ W, T x = x := by
  intro x hx
  have hd : T (T x - x) = T x - x := h x hx
  -- ⟨Tx, Tx-x⟩ = ⟨Tx, T(Tx-x)⟩ = ⟨x, Tx-x⟩, since T is an isometry and T(Tx-x) = Tx-x
  have h1 : inner ℝ (T x) (T x - x) = inner ℝ x (T x - x) := by
    calc inner ℝ (T x) (T x - x) = inner ℝ (T x) (T (T x - x)) := by rw [hd]
      _ = inner ℝ x (T x - x) := T.inner_map_map x (T x - x)
  -- hence ‖Tx - x‖² = ⟨Tx,Tx-x⟩ - ⟨x,Tx-x⟩ = 0
  have h2 : inner ℝ (T x - x) (T x - x) = 0 := by
    rw [inner_sub_left, h1, sub_self]
  have h3 : T x - x = 0 := inner_self_eq_zero.mp h2
  exact sub_eq_zero.mp h3

end Work.Mostow
