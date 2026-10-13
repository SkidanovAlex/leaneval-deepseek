import Mathlib
import Submission.Work.WilC2.BndDefs

open Set

namespace Work.WilVP

/-- If no point of the open interval `(p₁,p₂)` is a boundary point of `D`, then `D` is constant
("all or nothing") on that interval: `x ∈ D` forces `(p₁,p₂) ⊆ D`.
Proof: `¬ IsBnd D y` means `y` is in the interior of `D` or of `Dᶜ` (an open interval around `y`
lies in `D`, respectively in `Dᶜ`); both interiors are open, they are disjoint, and they cover
`(p₁,p₂)`; `x` lies in the first one, so by connectedness of the open interval the whole
interval does. -/
theorem piece_subset_of_notBnd {D : Set ℝ} {p₁ p₂ x : ℝ} (h₁ : p₁ < x) (h₂ : x < p₂)
    (hD : ∀ y ∈ Set.Ioo p₁ p₂, ¬ Work.WilC2.IsBnd D y) (hx : x ∈ D) :
    Set.Ioo p₁ p₂ ⊆ D := by
  have hxIoo : x ∈ Set.Ioo p₁ p₂ := ⟨h₁, h₂⟩
  -- The two interiors cover the open interval: a non-boundary point lies in one of them.
  have hcover : Set.Ioo p₁ p₂ ⊆ interior D ∪ interior Dᶜ := by
    intro y hy
    have h := hD y hy
    rw [Work.WilC2.isBnd_iff] at h
    by_cases hA : ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (y - ε) (y + ε) ⊆ D
    · obtain ⟨ε, hε, hsub⟩ := hA
      left
      exact mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (Work.WilC2.mem_Ioo_self hε)) hsub)
    · right
      have hB : ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (y - ε) (y + ε) ⊆ Dᶜ := by
        by_contra hcon
        exact h ⟨hA, hcon⟩
      obtain ⟨ε, hε, hsub⟩ := hB
      exact mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (Work.WilC2.mem_Ioo_self hε)) hsub)
  -- The two interiors are disjoint.
  have hdisj : Set.Ioo p₁ p₂ ∩ (interior D ∩ interior Dᶜ) = ∅ := by
    have h0 : interior D ∩ interior Dᶜ = ∅ := by
      rw [← interior_inter, inter_compl_self, interior_empty]
    rw [h0, inter_empty]
  -- `(p₁,p₂)` is preconnected, so it lies inside one of the two covering open sets.
  rcases (isPreconnected_iff_subset_of_disjoint.mp (isPreconnected_Ioo (a := p₁) (b := p₂)))
      (interior D) (interior Dᶜ) isOpen_interior isOpen_interior hcover hdisj with h | h
  · intro y hy
    exact interior_subset (h hy)
  · exfalso
    have hxcon : x ∈ interior Dᶜ := h hxIoo
    have hxd : x ∈ Dᶜ := interior_subset hxcon
    exact hxd hx

end Work.WilVP
