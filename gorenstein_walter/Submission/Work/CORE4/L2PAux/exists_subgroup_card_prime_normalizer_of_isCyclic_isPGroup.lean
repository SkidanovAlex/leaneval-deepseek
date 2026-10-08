import Mathlib

namespace Work.CORE4.L2PAux

/-- If `g` has order `ℓ ^ m` with `ℓ` prime and `1 ≤ m`, then `g ^ (ℓ ^ (m - 1))`
has order `ℓ`. -/
lemma orderOf_pow_prime {G : Type*} [Group G] {g : G} {ℓ m : ℕ} (hℓ : ℓ.Prime)
    (hord : orderOf g = ℓ ^ m) (hm : 1 ≤ m) : orderOf (g ^ (ℓ ^ (m - 1))) = ℓ := by
  have hmul : ℓ ^ (m - 1) * ℓ = ℓ ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  have hpow : (g ^ (ℓ ^ (m - 1))) ^ ℓ = 1 := by
    rw [← pow_mul, hmul, ← hord]
    exact pow_orderOf_eq_one g
  have hdvd : orderOf (g ^ (ℓ ^ (m - 1))) ∣ ℓ := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hne : g ^ (ℓ ^ (m - 1)) ≠ 1 := by
    intro h
    have hdvd2 : orderOf g ∣ ℓ ^ (m - 1) := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hord] at hdvd2
    exact Nat.not_dvd_of_pos_of_lt (pow_pos hℓ.pos _)
      (Nat.pow_lt_pow_right hℓ.one_lt (by omega)) hdvd2
  rcases hℓ.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

theorem exists_subgroup_card_prime_normalizer_of_isCyclic_isPGroup {G : Type*} [Group G] {ℓ m : ℕ} (hℓ : ℓ.Prime) (P T : Subgroup G) (hcyc : IsCyclic P) (hcard : Nat.card P = ℓ ^ m) (hm : 1 ≤ m) (hTN : T ≤ Subgroup.normalizer (P : Set G)) : ∃ Y : Subgroup G, Y ≤ P ∧ Nat.card Y = ℓ ∧ T ≤ Subgroup.normalizer (Y : Set G) ∧ P ≤ Subgroup.centralizer (Y : Set G) := by
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top P).mp hcyc
  have hord : orderOf g = ℓ ^ m := by rw [← Nat.card_zpowers, hg, hcard]
  set n := ℓ ^ (m - 1) with hn
  set y := g ^ n with hy
  have hyP : y ∈ P := by rw [hy, hn, ← hg]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _
  have hYP : Subgroup.zpowers y ≤ P := by rw [Subgroup.zpowers_le]; exact hyP
  have hpowcomm : ∀ k : ℤ, (g ^ k) ^ n = (g ^ n) ^ k := by
    intro k
    rw [← zpow_natCast (g ^ k) n, ← zpow_mul, ← zpow_natCast g n, ← zpow_mul, mul_comm]
  have key : ∀ s : G, s ∈ Subgroup.normalizer (P : Set G) →
      ∀ h ∈ Subgroup.zpowers y, s * h * s⁻¹ ∈ Subgroup.zpowers y := by
    intro s hs h hh
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hj]
    have hsy : s * y * s⁻¹ ∈ Subgroup.zpowers y := by
      have hsg : s * g * s⁻¹ ∈ Subgroup.zpowers g := by
        rw [hg]
        exact (Subgroup.mem_set_normalizer_iff.mp hs g).mp (by rw [← hg]; exact Subgroup.mem_zpowers g)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsg
      rw [show s * y * s⁻¹ = y ^ k from ?_]
      · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) k
      rw [hy, show s * g ^ n * s⁻¹ = (s * g * s⁻¹) ^ n from (conj_pow).symm, ← hk, hpowcomm]
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hsy j
  refine ⟨Subgroup.zpowers y, hYP, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, hy, hn]; exact orderOf_pow_prime hℓ hord hm
  · intro t ht
    have htN : t ∈ Subgroup.normalizer (P : Set G) := hTN ht
    have htinvN : t⁻¹ ∈ Subgroup.normalizer (P : Set G) := (Subgroup.normalizer (P : Set G)).inv_mem htN
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · exact key t htN h
    · intro hh
      have hthis := key t⁻¹ htinvN (t * h * t⁻¹) hh
      have hconj : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
      rwa [hconj] at hthis
  · exact le_trans (Subgroup.le_centralizer P) (Subgroup.centralizer_le hYP)

end Work.CORE4.L2PAux
