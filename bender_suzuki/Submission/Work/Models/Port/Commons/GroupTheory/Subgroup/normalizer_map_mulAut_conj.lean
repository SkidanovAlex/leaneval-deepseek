import Mathlib.Algebra.Group.Subgroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem normalizer_map_mulAut_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom) : Set G) =
      (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom := by
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hf : Function.Surjective f := (MulAut.conj g).surjective
  have hi : Function.Injective f := (MulAut.conj g).injective
  have hkey :
      (Subgroup.normalizer ((H.map f) : Set G)).comap f = Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range (MonoidHom.range_eq_top.mpr hf ▸ le_top)]
    rw [Subgroup.comap_map_eq_self_of_injective hi H]
  rw [← hkey, Subgroup.map_comap_eq_self_of_surjective hf]

end Commons.GroupTheory.Subgroup