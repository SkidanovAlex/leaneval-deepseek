import Mathlib
import Submission.Work.BG.Defs

/-!
# Area BG: elements of `K ∖ N` have even order when `K/N` is a `2`-group

If `N ≤ K ≤ G` with `N ◁ K` and the quotient `K/N` is a `2`-group, then every `x ∈ K`
with `x ∉ N` has even order.

The mathematics is elementary: the image of `x` in `K/N` is nontrivial, so its order is a
power of `2` strictly bigger than `1`, hence even; and this order divides `orderOf x` because
`orderOf ⟨x, hxK⟩ = orderOf x` and the quotient map is a homomorphism.
-/

namespace Work.BG

theorem two_dvd_orderOf_of_isPGroup_quotient {G : Type} [Group G] [Finite G] (K N : Subgroup G)
    (hNK : N ≤ K) [hN : (N.subgroupOf K).Normal] (h2 : IsPGroup 2 (↥K ⧸ N.subgroupOf K))
    {x : G} (hxK : x ∈ K) (hxN : x ∉ N) : 2 ∣ orderOf x := by
  -- The image of `x` in `K/N` is nontrivial because `x ∉ N`.
  have hx'N : (⟨x, hxK⟩ : ↥K) ∉ N.subgroupOf K := by
    rw [Subgroup.mem_subgroupOf]
    exact hxN
  have hv_ne : (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : ↥K ⧸ N.subgroupOf K) ≠ 1 := by
    rw [ne_eq, QuotientGroup.eq_one_iff]
    exact hx'N
  -- Its order is a power of `2`, and since it is nontrivial this power is `2 ^ l` with `l ≥ 1`.
  obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow.mp h2) (QuotientGroup.mk (⟨x, hxK⟩ : ↥K))
  have h2dvd_q : 2 ∣ orderOf (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : ↥K ⧸ N.subgroupOf K) := by
    obtain ⟨l, hl, hleq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk
    have hl1 : 1 ≤ l := by
      rcases Nat.eq_zero_or_pos l with h | h
      · exfalso
        rw [h, pow_zero] at hleq
        exact hv_ne (orderOf_eq_one_iff.mp hleq)
      · exact h
    rw [hleq]
    simpa only [pow_one] using pow_dvd_pow 2 hl1
  -- This order divides `orderOf x`, since `orderOf ⟨x, hxK⟩ = orderOf x` and the quotient map
  -- is a homomorphism.
  have hdvd : orderOf (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : ↥K ⧸ N.subgroupOf K) ∣ orderOf x := by
    rw [← Subgroup.orderOf_mk x hxK]
    exact orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf K)) _
  exact h2dvd_q.trans hdvd

end Work.BG
