import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Order.Atoms

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem isCoatom_map_mulAut_conj {G : Type*} [Group G] {H : Subgroup G} (h : IsCoatom H) (g : G) :
    IsCoatom (H.map (MulAut.conj g).toMonoidHom) := by
  simpa using (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g)) H).mpr h

end Commons.GroupTheory.Subgroup