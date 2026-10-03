import Mathlib

namespace Work.PlanarSC

/-- A connected component of a compact set is closed in the ambient space: the set is
closed, and a connected component is closed inside it. -/
theorem isClosed_connectedComponentIn_of_isCompact {S : Set ℂ} (hS : IsCompact S) (a : ℂ) :
    IsClosed (connectedComponentIn S a) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  by_cases ha : a ∈ S
  · have hzS : z ∈ S :=
      (hS.isClosed.closure_subset_iff.mpr (connectedComponentIn_subset S a)) hz
    have hzcl2 : z ∈ closure (Subtype.val '' connectedComponent (⟨a, ha⟩ : S)) := by
      rwa [connectedComponentIn_eq_image ha] at hz
    have hzcl' : (⟨z, hzS⟩ : S) ∈ closure (connectedComponent (⟨a, ha⟩ : S)) :=
      closure_subtype.mpr hzcl2
    have hclosed : IsClosed (connectedComponent (⟨a, ha⟩ : S)) := isClosed_connectedComponent
    have hmem : (⟨z, hzS⟩ : S) ∈ connectedComponent (⟨a, ha⟩ : S) :=
      ((hclosed.closure_subset_iff).mpr (le_refl _)) hzcl'
    rw [connectedComponentIn_eq_image ha]
    exact ⟨⟨z, hzS⟩, hmem, rfl⟩
  · rw [connectedComponentIn_eq_empty ha] at hz
    simp at hz

end Work.PlanarSC
