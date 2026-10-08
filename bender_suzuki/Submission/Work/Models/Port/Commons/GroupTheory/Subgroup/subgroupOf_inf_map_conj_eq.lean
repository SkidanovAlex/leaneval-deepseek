import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Map

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem subgroupOf_inf_map_conj_eq {G : Type*} [Group G] (H K : Subgroup G) (h : H ≤ K)
    (g : ↥K) :
    H.subgroupOf K ⊓ (H.subgroupOf K).map (MulAut.conj g).toMonoidHom =
      (H ⊓ H.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf K := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨hxH, y, hyH, hyx⟩
    exact ⟨hxH, (y : G), hyH, by rw [← hyx]; simp [MulAut.conj_apply]⟩
  · rintro ⟨hxH, y, hyH, hyx⟩
    exact ⟨hxH, ⟨y, h hyH⟩, hyH, by
      apply Subtype.ext
      rw [← hyx]
      simp [MulAut.conj_apply]⟩

end Commons.GroupTheory.Subgroup