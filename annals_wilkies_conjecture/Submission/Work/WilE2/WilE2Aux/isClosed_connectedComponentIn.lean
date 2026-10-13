import Mathlib

namespace Work.WilE2.WilE2Aux

theorem isClosed_connectedComponentIn {α : Type*} [TopologicalSpace α] {F : Set α}
    (hF : IsClosed F) (x : α) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · -- `connectedComponentIn F x` is the image of the connected component of `x`
    -- in the closed subspace `F` under the coercion `F → α`, which is a closed map.
    rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ (isClosed_connectedComponent (x := (⟨x, hx⟩ : F)))
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

end Work.WilE2.WilE2Aux
