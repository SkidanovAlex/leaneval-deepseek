import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CORE3.J4

/-- Auxiliary: in a finite group `G` of order `6`, if `a` has order `3`, `b` has order `2`
and `a` and `b` commute, then `G` is commutative.

This is the group-theoretic core of `J4QuotientStep`: a group of order `6` containing commuting
elements of orders `3` and `2` is the product `⟨a⟩⟨b⟩`, hence commutative. -/
theorem isMulCommutative_of_card_six {G : Type} [Group G] [Finite G] (hG : Nat.card G = 6)
    {a b : G} (ha : orderOf a = 3) (hb : orderOf b = 2) (hab : Commute a b) :
    IsMulCommutative G := by
  have hPcard : Nat.card ↥(Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, ha]
  have hPindex : (Subgroup.zpowers a).index = 2 := by
    have := Subgroup.index_mul_card (Subgroup.zpowers a)
    rw [hG, hPcard] at this
    omega
  have hb_notmem : b ∉ Subgroup.zpowers a := by
    intro hmem
    have hdvd := orderOf_dvd_of_mem_zpowers hmem
    rw [hb, ha] at hdvd
    exact absurd hdvd (by norm_num)
  have hsup : Subgroup.zpowers a ⊔ Subgroup.zpowers b = ⊤ := by
    refine Subgroup.index_eq_one.mp ?_
    have hdvd : (Subgroup.zpowers a ⊔ Subgroup.zpowers b).index ∣ 2 := by
      have := Subgroup.index_dvd_of_le
        (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
      rwa [hPindex] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exfalso
      have hsupcard : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 3 := by
        have := Subgroup.index_mul_card (Subgroup.zpowers a ⊔ Subgroup.zpowers b)
        rw [hG, h] at this
        omega
      have hPeq : Subgroup.zpowers a = Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hsupcard, hPcard])
      have hbin : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
        (le_sup_right : Subgroup.zpowers b ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
          (Subgroup.mem_zpowers b)
      exact hb_notmem (hPeq.symm ▸ hbin)
  have hpair : ({a, b} : Set G).Pairwise Commute := Set.pairwise_pair_of_symm_of_refl.mpr hab
  have hXmem : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hYmem : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Subgroup.closure ({a, b} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hXmem) (Subgroup.zpowers_le.mpr hYmem)
  have hcl : Subgroup.closure ({a, b} : Set G) = ⊤ :=
    le_antisymm le_top (hsup ▸ hle)
  exact Function.Surjective.isMulCommutative (f := Subgroup.topEquiv (G := G))
    (Subgroup.topEquiv (G := G)).surjective
    (hcl ▸ Subgroup.isMulCommutative_closure hpair)

theorem J4QuotientStep {H : Type} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hN : N.index = 6) (hnab : ¬ IsMulCommutative (H ⧸ N))
    {x s : H} (hx3 : orderOf x = 3) (hxN : x ∉ N) (hs2 : orderOf s = 2) (hc : x * s = s * x) :
    s ∈ N := by
  have hcard : Nat.card (H ⧸ N) = 6 := by
    rw [← Subgroup.index_eq_card N]; exact hN
  have hX3 : orderOf (x : H ⧸ N) = 3 := by
    have hdvd : orderOf (x : H ⧸ N) ∣ 3 := by
      simpa [QuotientGroup.mk'_apply, hx3] using orderOf_map_dvd (QuotientGroup.mk' N) x
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd ((QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h)) hxN
    · exact h
  have hSdvd : orderOf (s : H ⧸ N) ∣ 2 := by
    simpa [QuotientGroup.mk'_apply, hs2] using orderOf_map_dvd (QuotientGroup.mk' N) s
  have hcomm : Commute (x : H ⧸ N) (s : H ⧸ N) := by
    have h1 : Commute x s := hc
    have h2 := h1.map (QuotientGroup.mk' N)
    simpa [QuotientGroup.mk'_apply] using h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hSdvd with hS1 | hS2
  · exact (QuotientGroup.eq_one_iff s).mp (orderOf_eq_one_iff.mp hS1)
  · exact absurd (isMulCommutative_of_card_six hcard hX3 hS2 hcomm) hnab

end Work.CORE3.J4
