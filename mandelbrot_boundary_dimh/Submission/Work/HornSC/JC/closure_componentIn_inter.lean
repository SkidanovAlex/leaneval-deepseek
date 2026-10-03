import Mathlib

namespace Work.HornSC.JC

/-- **A component of an open subset of `ℂ` is closed in it.** -/
theorem closure_componentIn_inter {V : Set ℂ} (x : ℂ) :
    closure (connectedComponentIn V x) ∩ V = connectedComponentIn V x := by
  by_cases hx : x ∈ V
  · -- If `x ∈ V`, the component is the image of a connected component of the subspace `V`,
    -- which is closed in `V`; closedness in the subspace is exactly `closure ∩ V = self`.
    rw [connectedComponentIn_eq_image hx]
    refine subset_antisymm ?_ ?_
    · rintro y ⟨hycl, hyV⟩
      have h := (isClosed_induced_iff' (f := ((↑) : V → ℂ))
        (s := connectedComponent (⟨x, hx⟩ : V))).mp isClosed_connectedComponent ⟨y, hyV⟩ hycl
      exact Set.mem_image_of_mem _ h
    · intro y hy
      refine ⟨subset_closure hy, ?_⟩
      obtain ⟨v, -, rfl⟩ := hy
      exact v.2
  · -- If `x ∉ V` the component is empty.
    rw [connectedComponentIn_eq_empty hx, closure_empty, Set.empty_inter]

end Work.HornSC.JC
