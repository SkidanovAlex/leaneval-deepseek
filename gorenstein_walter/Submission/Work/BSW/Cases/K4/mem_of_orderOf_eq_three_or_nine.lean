import Mathlib

namespace Work.BSW.Cases.K4

/-- In a group `N` of order `36` with a normal subgroup `Q` of order `9`, every element of order
`3` or `9` already lies in `Q`.

Indeed `Q` is normal of index `4` in `N`, so the quotient `N ⧸ Q` has order `4`.  The image of an
element `x` of order `3` (or `9`) under `N → N ⧸ Q` has order dividing both `3` (resp. `9`) and
`4`, hence trivial, so `x` lies in the kernel `Q` of that map. -/
theorem mem_of_orderOf_eq_three_or_nine {G : Type} [Group G]
    (N Q : Subgroup G) (hQN : Q ≤ N) (hN : Nat.card ↥N = 36) (hQ : Nat.card ↥Q = 9)
    (hQnorm : (Q.subgroupOf N).Normal) {x : G} (hx : x ∈ N)
    (h3 : orderOf x = 3 ∨ orderOf x = 9) : x ∈ Q := by
  let H : Subgroup N := Q.subgroupOf N
  haveI : H.Normal := hQnorm
  -- `H` has order `9`
  have hHcard : Nat.card ↥H = 9 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
    rw [hQ] at h
    exact h
  -- the quotient `N ⧸ H` has order `36 / 9 = 4`
  have hquot : Nat.card (N ⧸ H) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (s := H)
    rw [hN, hHcard] at h
    omega
  -- the image of `x` in the quotient has order dividing both `orderOf x` and `4`
  have hdvd1 : orderOf (QuotientGroup.mk' H (⟨x, hx⟩ : N)) ∣ orderOf x := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' H) (⟨x, hx⟩ : N)
    rwa [Subgroup.orderOf_mk x hx] at h1
  have hone : orderOf (QuotientGroup.mk' H (⟨x, hx⟩ : N)) = 1 := by
    have hdvd4 : orderOf (QuotientGroup.mk' H (⟨x, hx⟩ : N)) ∣ 4 := by
      rw [← hquot]
      exact orderOf_dvd_natCard _
    rcases h3 with h3 | h3
    · have hb : orderOf (QuotientGroup.mk' H (⟨x, hx⟩ : N)) ∣ 3 := h3 ▸ hdvd1
      have hcd := Nat.dvd_gcd hb hdvd4
      have hg : Nat.gcd 3 4 = 1 := by decide
      rw [hg] at hcd
      exact Nat.dvd_one.mp hcd
    · have hb : orderOf (QuotientGroup.mk' H (⟨x, hx⟩ : N)) ∣ 9 := h3 ▸ hdvd1
      have hcd := Nat.dvd_gcd hb hdvd4
      have hg : Nat.gcd 9 4 = 1 := by decide
      rw [hg] at hcd
      exact Nat.dvd_one.mp hcd
  -- hence `x ∈ H = Q` in `N`, i.e. `x ∈ Q` in `G`
  have hmem : (⟨x, hx⟩ : N) ∈ H := by
    rw [← QuotientGroup.eq_one_iff, ← orderOf_eq_one_iff]
    simpa using hone
  simpa using Subgroup.mem_subgroupOf.mp hmem

end Work.BSW.Cases.K4
