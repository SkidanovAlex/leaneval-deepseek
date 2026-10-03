import Mathlib

namespace Work.Horn.Basin

/-- If every compact subset of `U` is contained in a simply connected subset of `U`,
then `U` itself is simply connected.

The content is that simple connectivity is detected by loops, and a loop has compact image:
any loop in `U` lies in a simply connected `V ⊆ U`, where it is null-homotopic, hence so in `U`.
Path-connectedness is similar, using the compact set `{x, y}`. -/
theorem simplyConnectedSpace_of_hulls {U : Set ℂ}
    (h : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ V : Set ℂ, IsSimplyConnected V ∧ K ⊆ V ∧ V ⊆ U) :
    SimplyConnectedSpace ↥U := by
  change IsSimplyConnected U
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  constructor
  · rw [isPathConnected_iff]
    constructor
    · -- `U` is nonempty: a simply connected hull of the empty set is nonempty.
      obtain ⟨V, hV, -, hVU⟩ := h ∅ isCompact_empty (Set.empty_subset U)
      obtain ⟨v, hv⟩ := hV.nonempty
      exact ⟨v, hVU hv⟩
    · -- any two points of `U` are joined inside `U`
      intro x hx y hy
      have hK : IsCompact ({(x : ℂ), y} : Set ℂ) := Set.Finite.isCompact (by simp)
      have hKU : ({(x : ℂ), y} : Set ℂ) ⊆ U := by
        intro z hz
        rcases (by simpa using hz : z = x ∨ z = y) with rfl | rfl <;> assumption
      obtain ⟨V, hV, hKV, hVU⟩ := h _ hK hKU
      obtain ⟨γ, hγ⟩ := hV.isPathConnected.joinedIn x (hKV (by simp)) y (hKV (by simp))
      exact ⟨γ, fun t => hVU (hγ t)⟩
  · -- any loop in `U` has compact image, so lies in a simply connected `V ⊆ U`
    intro x p hp
    have hK : IsCompact (Set.range p) := isCompact_range p.continuous
    have hKU : Set.range p ⊆ U := by
      rintro z ⟨t, rfl⟩
      exact hp t
    obtain ⟨V, hV, hKV, hVU⟩ := h _ hK hKU
    obtain ⟨F, hF⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hV).2 x p
      (fun t => hKV ⟨t, rfl⟩)
    exact ⟨F, fun t => hVU (hF t)⟩

end Work.Horn.Basin
