import Mathlib

open Set

set_option linter.unusedVariables false

namespace Work.BoxShrink.PinchOff

/-- If `J` is closed and its complement is split into two disjoint nonempty open
preconnected sets `U`, `V`, and `A` is a compact set whose `J`-complement `A \ J` is
nonempty and preconnected while `A \ J ⊆ interior A` and `A ⊆ closure (A \ J)`,
then `A` is the closure of one of the two sides: `A = closure V` or `A = closure U`.

The proof: `A \ J ⊆ U ∪ V` is preconnected inside the disjoint open cover `{U, V}`,
so it lies entirely in `U` or entirely in `V`; suppose it lies in `U`.  Then
`U ∩ A = A \ J` and in particular `U ∩ A ⊆ interior A`, while `A` closed gives
`U ∩ A` closed in `U`; so `U ∩ A` is clopen in the preconnected `U` and, being
nonempty, equals `U`. Hence `U ⊆ A`, giving `closure U ⊆ A`, and
`A ⊆ closure (A \ J) ⊆ closure U`; thus `A = closure U`. -/
theorem side_of_compact_sheet {J U V A : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hUpc : IsPreconnected U) (hVpc : IsPreconnected V) (hUne : U.Nonempty) (hVne : V.Nonempty)
    (hdisj : Disjoint U V) (hunion : U ∪ V = Jᶜ) (hJ : IsClosed J)
    (hAc : IsCompact A) (hAne : (A \ J).Nonempty) (hApc : IsPreconnected (A \ J))
    (hAint : A \ J ⊆ interior A) (hAcl : A ⊆ closure (A \ J)) :
    A = closure V ∨ A = closure U := by
  obtain hAclosed := hAc.isClosed
  have hWU : U ⊆ Jᶜ := by rw [← hunion]; exact subset_union_left
  have hWV : V ⊆ Jᶜ := by rw [← hunion]; exact subset_union_right
  have hsub : A \ J ⊆ U ∪ V := by rw [hunion]; intro x hx; exact hx.2
  -- For any side `W` containing `A \ J`, the whole side is contained in `A`.
  have key : ∀ W : Set ℂ, IsOpen W → IsPreconnected W → W ⊆ Jᶜ → A \ J ⊆ W → W ⊆ A := by
    intro W _ hWpc hWJ hAW
    have h1 : W ∩ A ⊆ A \ J := fun x hx => ⟨hx.2, fun hxJ => hWJ hx.1 hxJ⟩
    have hWsub : W ⊆ interior A := by
      refine hWpc.subset_left_of_subset_union isOpen_interior hAclosed.isOpen_compl ?_ ?_ ?_
      · exact Disjoint.mono_left interior_subset disjoint_compl_right
      · intro x hx
        by_cases hxA : x ∈ A
        · exact Or.inl (hAint (h1 ⟨hx, hxA⟩))
        · exact Or.inr hxA
      · obtain ⟨x, hx⟩ := hAne
        exact ⟨x, hAW hx, hAint hx⟩
    exact fun x hx => interior_subset (hWsub hx)
  rcases hApc.subset_or_subset hUo hVo hdisj hsub with hAU | hAV
  · -- `A \ J ⊆ U`, so `A = closure U`.
    right
    have hUA := key U hUo hUpc hWU hAU
    exact le_antisymm (Subset.trans hAcl (closure_mono hAU)) (closure_minimal hUA hAclosed)
  · -- `A \ J ⊆ V`, so `A = closure V`.
    left
    have hVA := key V hVo hVpc hWV hAV
    exact le_antisymm (Subset.trans hAcl (closure_mono hAV)) (closure_minimal hVA hAclosed)

end Work.BoxShrink.PinchOff
