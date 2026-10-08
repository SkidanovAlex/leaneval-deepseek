import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIShadow

theorem isCoatom_subgroupOf_of_maximal {G : Type} [Group G] {K F : Subgroup G} (hKF : K < F)
    (hmax : ∀ M : Subgroup G, K ≤ M → M ≤ F → M = K ∨ M = F) :
    IsCoatom (K.subgroupOf F) := by
  constructor
  · -- `K.subgroupOf F` is not the whole of `F`, since `K ≠ F`.
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact hKF.ne (le_antisymm hKF.le h)
  · -- Maximality: any larger subgroup of `F` is `⊤`.
    intro b hb
    have hle : K.subgroupOf F ≤ b := hb.le
    -- `b` is the `subgroupOf F`-image of its image in `G`.
    have hmap : (b.map F.subtype).subgroupOf F = b := by
      rw [← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective F.subtype_injective b
    -- `K` lies below the image of `b` in `G`.
    have hKmap : K ≤ b.map F.subtype := by
      intro k hk
      exact ⟨⟨k, hKF.le hk⟩, hle ((Subgroup.mem_subgroupOf).2 hk), rfl⟩
    have hMF : b.map F.subtype ≤ F := Subgroup.map_subtype_le b
    rcases hmax (b.map F.subtype) hKmap hMF with hM | hM
    · -- the image is `K`, contradicting strictness
      exact absurd (show b = K.subgroupOf F by rw [← hmap, hM]).symm hb.ne
    · -- the image is `F`, so `b = ⊤`
      rw [← hmap, hM, Subgroup.subgroupOf_self]

end Work.AppXIShadow
