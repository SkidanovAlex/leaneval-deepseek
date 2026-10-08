import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Map

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem map_mulAut_conj {G H : Type*} [Group G] [Group H] (φ : G →* H) (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g).toMonoidHom).map φ
      = (K.map φ).map (MulAut.conj (φ g)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨φ k, ⟨k, hk, rfl⟩, by simp [MulAut.conj_apply, map_mul]⟩
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨(MulAut.conj g).toMonoidHom k, ⟨k, hk, rfl⟩, by simp [MulAut.conj_apply, map_mul]⟩

end Commons.GroupTheory.Subgroup