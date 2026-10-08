import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.Transport

theorem hall_map_mulAut_conj {G G' : Type*} [Group G] [Group G'] (f : G →* G') (H : Subgroup G)
    (g : G) : (H.map f).map (MulAut.conj (f g)).toMonoidHom =
      (H.map (MulAut.conj g).toMonoidHom).map f := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext h
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

end Work.Hall.Transport
