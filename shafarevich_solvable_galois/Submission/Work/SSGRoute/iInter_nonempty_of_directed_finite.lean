import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Finite intersection property for a downward-directed family of nonempty sets.**

If `F : α → Set β` is a family of nonempty subsets of a finite type `β` which is
downward directed (`F c ⊆ F a ∩ F b` for suitable `c`), then the total intersection
`⋂ a, F a` is nonempty.

The proof picks a `⊆`-minimal member `F a₀` of the (finite) range of `F`; directedness
forces `F a₀ ⊆ F b` for every `b`, and `F a₀` is nonempty. -/
theorem iInter_nonempty_of_directed_finite {α β : Type} [Nonempty α] [Finite β] (F : α → Set β)
    (hne : ∀ a, (F a).Nonempty) (hdir : ∀ a b, ∃ c, F c ⊆ F a ∩ F b) :
    (⋂ a, F a).Nonempty := by
  classical
  -- `Set β` is finite, so the range of `F` is a finite nonempty set of subsets of `β`.
  have hfin : (Set.range F).Finite := Set.toFinite _
  -- Take a `⊆`-minimal element `F a₀` of the range.
  obtain ⟨s₀, hs₀, hmin⟩ := hfin.exists_minimal (Set.range_nonempty F)
  obtain ⟨a₀, rfl⟩ := hs₀
  -- Directedness gives `F c ⊆ F a₀` for some `c`; minimality turns this into `F a₀ ⊆ F c`,
  -- and `F c ⊆ F b`, so `F a₀ ⊆ F b` for every `b`.
  have key : ∀ b, F a₀ ⊆ F b := by
    intro b
    obtain ⟨c, hc⟩ := hdir a₀ b
    exact (hmin (Set.mem_range_self c) (hc.trans Set.inter_subset_left)).trans
      (hc.trans Set.inter_subset_right)
  exact (hne a₀).mono fun x hx => Set.mem_iInter.mpr fun b => key b hx

end Work.SSGRoute
