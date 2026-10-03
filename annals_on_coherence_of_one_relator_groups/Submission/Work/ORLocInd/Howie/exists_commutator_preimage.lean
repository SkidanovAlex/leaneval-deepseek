import Mathlib

namespace Work.ORLocInd.Howie

/-- A surjective homomorphism maps the commutator subgroup onto the commutator subgroup. -/
theorem exists_commutator_preimage {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {h : H} (hh : h ∈ commutator H) :
    ∃ c : G, c ∈ commutator G ∧ f c = h := by
  have key : (commutator G).map f = commutator H := by
    rw [map_commutator_eq G f, MonoidHom.range_eq_top.mpr hf]
    rfl
  rw [← key] at hh
  exact Subgroup.mem_map.mp hh

end Work.ORLocInd.Howie
