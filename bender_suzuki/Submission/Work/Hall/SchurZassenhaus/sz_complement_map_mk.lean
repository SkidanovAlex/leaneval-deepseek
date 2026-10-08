import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.SchurZassenhaus

theorem sz_complement_map_mk {G : Type*} [Group G] [Finite G] {N M H : Subgroup G} [N.Normal]
    [M.Normal] (hMN : M ≤ N) (h : N.IsComplement' H) :
    (N.map (QuotientGroup.mk' M)).IsComplement' (H.map (QuotientGroup.mk' M)) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · -- The images of `N` and `H` in `G ⧸ M` intersect trivially.
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxN, hxH⟩ := hx
    rw [Subgroup.mem_map] at hxN hxH
    obtain ⟨n, hn, hn_eq⟩ := hxN
    obtain ⟨k, hk, hk_eq⟩ := hxH
    -- `mk' M n = mk' M k` forces `k⁻¹ * n ∈ M ≤ N`, hence `k ∈ N`.
    have hkn : k⁻¹ * n ∈ M := QuotientGroup.eq.mp (hk_eq.trans hn_eq.symm)
    have hkN : k ∈ N := by
      have h2 : k⁻¹ * n ∈ N := hMN hkn
      have hk1 : k⁻¹ ∈ N := by
        simpa using N.mul_mem h2 (N.inv_mem hn)
      simpa using N.inv_mem hk1
    -- `H ⊓ N = ⊥`, so `k = 1`, and thus `x = mk' M n = mk' M k = 1`.
    have hkbot : k ∈ (⊥ : Subgroup G) :=
      (disjoint_iff_inf_le.mp h.disjoint) ⟨hkN, hk⟩
    have hk1 : k = 1 := by simpa using hkbot
    rw [Subgroup.mem_bot]
    have hnk : QuotientGroup.mk' M n = QuotientGroup.mk' M k := hn_eq.trans hk_eq.symm
    rw [← hn_eq, hnk, hk1, map_one]
  · -- `N * H = ⊤` maps onto `(N.map π) * (H.map π) = ⊤`.
    rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, Subgroup.IsComplement.mul_eq h,
      Set.image_univ, Set.range_eq_univ]
    exact QuotientGroup.mk'_surjective M

end Work.Hall.SchurZassenhaus
