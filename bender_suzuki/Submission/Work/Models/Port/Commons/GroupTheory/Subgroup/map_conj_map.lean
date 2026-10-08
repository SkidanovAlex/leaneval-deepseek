import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Map

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem map_conj_map {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (A : Subgroup G) (h : G) :
    Subgroup.map φ (A.map (MulAut.conj h).toMonoidHom) =
      (Subgroup.map φ A).map (MulAut.conj (φ h)).toMonoidHom := by
  have hhoms : φ.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (φ h)).toMonoidHom.comp φ := by
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  calc
    Subgroup.map φ (A.map (MulAut.conj h).toMonoidHom)
        = A.map (φ.comp (MulAut.conj h).toMonoidHom) := by
          rw [Subgroup.map_map A φ (MulAut.conj h).toMonoidHom]
    _ = A.map ((MulAut.conj (φ h)).toMonoidHom.comp φ) := by
          rw [hhoms]
    _ = (Subgroup.map φ A).map (MulAut.conj (φ h)).toMonoidHom := by
          rw [← Subgroup.map_map A (MulAut.conj (φ h)).toMonoidHom φ]

end Commons.GroupTheory.Subgroup