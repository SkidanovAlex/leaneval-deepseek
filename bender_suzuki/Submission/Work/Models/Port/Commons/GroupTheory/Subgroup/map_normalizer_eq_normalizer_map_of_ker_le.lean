import Mathlib.Algebra.Group.Subgroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem map_normalizer_eq_normalizer_map_of_ker_le {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Surjective φ) {K : Subgroup G} (hker : φ.ker ≤ K) :
    Subgroup.normalizer ((K.map φ : Subgroup H) : Set H)
      = (Subgroup.normalizer (K : Set G)).map φ := by
  apply le_antisymm
  · calc Subgroup.normalizer ((K.map φ : Subgroup H) : Set H)
        = ((Subgroup.normalizer ((K.map φ : Subgroup H) : Set H)).comap φ).map φ :=
          (Subgroup.map_comap_eq_self_of_surjective hφ _).symm
      _ ≤ (Subgroup.normalizer (K : Set G)).map φ :=
          Subgroup.map_mono (by
            have h1 := Subgroup.le_normalizer_comap (f := φ)
              (H := (K.map φ : Subgroup H))
            rwa [Subgroup.comap_map_eq_self hker] at h1)
  · exact Subgroup.le_normalizer_map φ

end Commons.GroupTheory.Subgroup