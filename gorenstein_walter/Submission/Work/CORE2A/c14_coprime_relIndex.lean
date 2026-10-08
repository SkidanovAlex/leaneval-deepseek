import Mathlib

namespace Work.CORE2A

/-- If `H ≤ K` and `H` is normal in `K`, then any `g ∈ K` whose order is coprime
to the relative index `[K : H]` already lies in `H`.

This is used in the CORE2A part of the Gorenstein–Walter argument: an element of a
subgroup `K` whose order is coprime to the index of a normal subgroup `H` lies in
`H`; equivalently, the quotient `K/H` has no elements of order coprime to its own
cardinality, so `g` dies in `K/H`. -/
theorem c14_coprime_relIndex {G : Type} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (hnorm : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) {g : G} (hg : g ∈ K)
    (hcop : Nat.Coprime (orderOf g) (H.relIndex K)) : g ∈ H := by
  -- `H` is normal when viewed inside `K`.
  haveI hN : (H.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff hHK).mpr fun h k hh hk => hnorm k hk h hh
  -- The image of `g` in the quotient `K ⧸ (H.subgroupOf K)`.
  let q : K ⧸ (H.subgroupOf K) := QuotientGroup.mk' (H.subgroupOf K) ⟨g, hg⟩
  -- Its order divides the order of `g` ...
  have hq1 : orderOf q ∣ orderOf g := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (H.subgroupOf K)) (⟨g, hg⟩ : K)
    rw [Subgroup.orderOf_mk] at h
    simpa only [q] using h
  -- ... and divides the cardinality of the quotient, which is `H.relIndex K`.
  have hq2 : orderOf q ∣ H.relIndex K := by
    simpa only [Subgroup.relIndex, Subgroup.index] using orderOf_dvd_natCard q
  -- Coprimality forces the image to be trivial.
  have hq : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop hq1 hq2
  have hqone : q = 1 := orderOf_eq_one_iff.mp hq
  -- Hence `g` lies in the kernel of the quotient map, i.e. in `H`.
  have hmem : (⟨g, hg⟩ : K) ∈ H.subgroupOf K := by
    rw [← QuotientGroup.ker_mk' (H.subgroupOf K), MonoidHom.mem_ker]
    simpa only [q] using hqone
  exact Subgroup.mem_subgroupOf.mp hmem

end Work.CORE2A
