import Mathlib.Algebra.Group.Subgroup.Ker

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem map_eq_top_iff_of_ker_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {S : Subgroup G} (h : f.ker ≤ S) :
    Subgroup.map f S = ⊤ ↔ S = ⊤ := by
  rw [← Subgroup.map_top_of_surjective f hf]
  exact ⟨fun h' => Subgroup.map_injective_of_ker_le f h le_top h', fun h' => by rw [h']⟩

end Commons.GroupTheory.Subgroup