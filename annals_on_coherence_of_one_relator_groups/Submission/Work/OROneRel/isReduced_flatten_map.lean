import Mathlib

namespace Work.OROneRel

/-- If `L` is a reduced list of letters of `β` and `f` sends each letter `p : β × Bool` to a
reduced word `f p` whose first and last letters are the image of `p` under the injective map of
generators `φ`, then the concatenation of the blocks `f p` along `L` is a reduced word. -/
theorem isReduced_flatten_map {β γ : Type*} (φ : β → γ) (hφ : Function.Injective φ)
    (f : β × Bool → List (γ × Bool)) (L : List (β × Bool))
    (hf : ∀ p, FreeGroup.IsReduced (f p))
    (hh : ∀ p, (f p).head? = some (φ p.1, p.2))
    (hl : ∀ p, (f p).getLast? = some (φ p.1, p.2))
    (hL : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced (L.map f).flatten := by
  -- each block is nonempty, so the list of blocks contains no `[]`
  have hne : ([] : List (γ × Bool)) ∉ L.map f := by
    intro h
    rcases List.mem_map.1 h with ⟨p, -, hp⟩
    have := hh p
    rw [hp] at this
    simp at this
  -- work with the underlying `List.IsChain` formulation
  rw [FreeGroup.IsReduced] at hL ⊢
  rw [List.isChain_flatten hne]
  refine ⟨?_, ?_⟩
  · -- every block is reduced
    intro l hl'
    rcases List.mem_map.1 hl' with ⟨p, -, rfl⟩
    exact hf p
  · -- the boundary between two consecutive blocks does not cancel
    rw [List.isChain_map]
    refine hL.imp fun a b hab => ?_
    intro x hx y hy hxy
    rw [hl a] at hx
    rw [hh b] at hy
    simp only [Option.mem_some_iff] at hx hy
    subst hx
    subst hy
    exact hab (hφ hxy)

end Work.OROneRel
