import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.Transport

/-- If `H ≤ X`, then pulling `H` back along the inclusion `X.subtype : X →* G` gives a subgroup of
`X` with the same underlying set as `H`; in particular it has the same cardinality. -/
theorem hall_map_comap_subtype_eq_of_le {G : Type*} [Group G] {X H : Subgroup G} (hH : H ≤ X) :
    (H.comap X.subtype).map X.subtype = H := by
  refine le_antisymm (Subgroup.map_comap_le _ _) ?_
  intro h hh
  exact ⟨⟨h, hH hh⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩

theorem hall_card_comap_subtype_of_le {G : Type*} [Group G] {X H : Subgroup G} (hH : H ≤ X) :
    Nat.card (H.comap X.subtype) = Nat.card H := by
  calc Nat.card (H.comap X.subtype)
      = Nat.card ((H.comap X.subtype).map X.subtype) :=
        (Subgroup.card_map_of_injective X.subtype_injective).symm
    _ = Nat.card H := by rw [hall_map_comap_subtype_eq_of_le hH]

end Work.Hall.Transport
