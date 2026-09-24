import Mathlib

namespace Work.SimplyConnected.ABS

/-- If `X` is covered by two path-connected sets whose intersection is nonempty, then `X` is
path-connected. -/
theorem pathConnectedSpace_of_cover {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ∪ B = Set.univ) (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hI : (A ∩ B).Nonempty) : PathConnectedSpace X := by
  have h : IsPathConnected (Set.univ : Set X) := by
    rw [← hAB]
    exact IsPathConnected.union hA hB hI
  obtain ⟨a, -, ha⟩ := h
  exact PathConnectedSpace.mk ⟨a⟩ fun x y =>
    (JoinedIn.trans (JoinedIn.symm (ha (Set.mem_univ x))) (ha (Set.mem_univ y))).joined

end Work.SimplyConnected.ABS
