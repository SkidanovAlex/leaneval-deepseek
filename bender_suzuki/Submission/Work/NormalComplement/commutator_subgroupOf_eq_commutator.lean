import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

theorem commutator_subgroupOf_eq_commutator {G : Type*} [Group G] (E : Subgroup G) :
    (⁅E, E⁆).subgroupOf E = commutator ↥E := by
  rw [← Subgroup.map_subtype_commutator E, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective E.subtype_injective]

end Work.NormalComplement
