import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.P3NeBot

set_option linter.style.haveILetI false in
/-- If `S` is a normal Sylow `2`-subgroup of `B` (i.e. `S ≤ B`, `B ≤ N_G(S)`, `S` is a
`2`-group and `2 ∤ [B : S]`) and `T ≤ N_G(B)`, then `T ≤ N_G(S)`: a normal Sylow subgroup of `B`
is normalised by everything normalising `B`.  Route: `(S.subgroupOf B)` is a normal Sylow
`2`-subgroup of `↥B`; for `t ∈ T`, `(S.map (MulAut.conj t).toMonoidHom).subgroupOf B` is a
`2`-subgroup of `↥B`, hence lies in the unique Sylow `S.subgroupOf B` (`IsPGroup.exists_le_sylow`
plus `Sylow.unique_of_normal`), so `t S t⁻¹ ≤ S`, and equality follows from equal cardinality. -/
theorem sylow_le_normalizer {G : Type} [Group G] [Finite G]
    {B S T : Subgroup G} (hSB : S ≤ B) (hSN : B ≤ Subgroup.normalizer (S : Set G))
    (hS2 : IsPGroup 2 S) (hidx : ¬ 2 ∣ (S.subgroupOf B).index)
    (hTB : T ≤ Subgroup.normalizer (B : Set G)) :
    T ≤ Subgroup.normalizer (S : Set G) := by
  -- `S.subgroupOf B` is a normal `2`-subgroup of `↥B`.
  have hNnormal : (S.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hSN
  haveI : (S.subgroupOf B).Normal := hNnormal
  have hN2 : IsPGroup 2 (S.subgroupOf B) :=
    hS2.comap_of_injective B.subtype Subtype.coe_injective
  -- It suffices to show `t * s * t⁻¹ ∈ S` for `t ∈ T`, `s ∈ S`.
  rw [Subgroup.le_normalizer_iff]
  intro t ht s hs
  -- `t S t⁻¹ ≤ B` because `t` normalises `B` and `S ≤ B`.
  have hRB : S.map (MulAut.conj t).toMonoidHom ≤ B := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp (hTB ht) x).mp (hSB hx)
  -- `t S t⁻¹ ≤ B` is a `2`-subgroup of `↥B`, hence is contained in `S.subgroupOf B`.
  have hR2 : IsPGroup 2 ((S.map (MulAut.conj t).toMonoidHom).subgroupOf B) :=
    (hS2.map (MulAut.conj t).toMonoidHom).comap_of_injective B.subtype Subtype.coe_injective
  obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow hR2
  have hNQ : S.subgroupOf B ≤ (Q : Subgroup ↥B) := IsPGroup.le_sylow_of_normal hN2 Q
  -- `S.subgroupOf B` is a Sylow of `↥B` (index coprime to `2`), so `Q = S.subgroupOf B`.
  have hQeq : (Q : Subgroup ↥B) = S.subgroupOf B :=
    (IsPGroup.toSylow hN2 hidx).is_maximal' Q.isPGroup' (by rwa [IsPGroup.toSylow_coe])
  have hRSS : S.map (MulAut.conj t).toMonoidHom ≤ S := by
    intro x hx
    have hxB : x ∈ B := hRB hx
    have hxP : (⟨x, hxB⟩ : ↥B) ∈ (S.map (MulAut.conj t).toMonoidHom).subgroupOf B :=
      Subgroup.mem_subgroupOf.mpr hx
    have hxN : (⟨x, hxB⟩ : ↥B) ∈ S.subgroupOf B := by
      have h := hPQ hxP
      rwa [hQeq] at h
    exact Subgroup.mem_subgroupOf.mp hxN
  exact hRSS (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)

end Work.ThreePoints.P3NeBot
