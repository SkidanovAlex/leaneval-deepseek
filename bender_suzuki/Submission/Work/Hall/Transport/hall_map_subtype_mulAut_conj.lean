import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.Transport

/-- Conjugation in a subgroup commutes with the inclusion into the ambient group:
the image under `X.subtype` of the conjugate of `H ≤ X` by `x : X` equals the conjugate of `H`
by `x` viewed inside `G`. -/
theorem hall_map_subtype_mulAut_conj {G : Type*} [Group G] {X H : Subgroup G} (hH : H ≤ X) (x : X) :
    ((H.comap X.subtype).map (MulAut.conj x).toMonoidHom).map X.subtype =
      H.map (MulAut.conj (x : G)).toMonoidHom := by
  have hcomp : X.subtype.comp (MulAut.conj x).toMonoidHom
      = (MulAut.conj (x : G)).toMonoidHom.comp X.subtype := by
    ext y
    simp [MulAut.conj_apply]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  rw [Subgroup.map_comap_eq_self]
  rw [Subgroup.range_subtype]
  exact hH

end Work.Hall.Transport
