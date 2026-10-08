import Mathlib

namespace Work.CORE4

/-- A `2`-element `t` of `M` that centralizes a `2`-subgroup `P ≤ M` of odd index (i.e. a
Sylow `2`-subgroup of `M`) lies in `P`.

`Q := P ⊔ Subgroup.zpowers t ≤ M` is a `2`-group (`IsPGroup.to_sup_of_normal_left'`), so
`Nat.card Q ∣ Nat.card M = P.relIndex M * Nat.card P`, and `Nat.card Q`, `Nat.card P` are powers
of `2`; coprimality with the odd `P.relIndex M` forces `Nat.card Q ≤ Nat.card P`, whence `Q = P`
as `P ≤ Q`. -/
theorem TMemOfSylow {G : Type} [Group G] [Finite G]
    (M P : Subgroup G) (t : G) (htM : t ∈ M) (ht2 : t ^ 2 = 1)
    (hP2 : IsPGroup 2 P) (hPM : P ≤ M) (hcent : ∀ x ∈ P, x * t = t * x)
    (hrel : ¬ 2 ∣ P.relIndex M) : t ∈ P := by
  classical
  -- `⟨t⟩` is a `2`-group, since `t ^ 2 = 1`.
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr ht2
  -- `t` commutes with `P`, hence normalizes it.
  have ht_cent : t ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcent x hx
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le_of_mem (Subgroup.centralizer_le_normalizer (P : Set G) ht_cent)
  -- `Q := P ⊔ ⟨t⟩` is a `2`-group.
  have hQ2 : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers t) :=
    IsPGroup.to_sup_of_normal_left' hP2 hT2 hnorm
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP2
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
  -- `Q ≤ M`, so `Nat.card Q ∣ Nat.card M`.
  have hQM : P ⊔ Subgroup.zpowers t ≤ M :=
    sup_le hPM (Subgroup.zpowers_le_of_mem htM)
  have hQdvd : Nat.card ↥(P ⊔ Subgroup.zpowers t) ∣ Nat.card ↥M := by
    have h := Subgroup.card_subgroup_dvd_card ((P ⊔ Subgroup.zpowers t).subgroupOf M)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv] at h
  have hMcard : Nat.card ↥M = P.relIndex M * Nat.card ↥P := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := M)
    rw [inf_eq_left.mpr hPM] at h
    exact h.symm
  -- `2 ^ n ∣ P.relIndex M * 2 ^ a`, and `P.relIndex M` is odd.
  have hdvd : 2 ^ n ∣ P.relIndex M * 2 ^ a := by
    rw [← hn, ← ha, ← hMcard]
    exact hQdvd
  have hodd : Odd (P.relIndex M) :=
    Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have hcop : Nat.Coprime (2 ^ n) (P.relIndex M) :=
    (Nat.coprime_two_left.mpr hodd).pow_left n
  have hdvd2 : 2 ^ n ∣ 2 ^ a :=
    hcop.dvd_of_dvd_mul_right (by rw [mul_comm]; exact hdvd)
  have hna : n ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd2
  -- Hence `Nat.card Q ≤ Nat.card P`, and since `P ≤ Q` this forces `Q = P`.
  have hcardle : Nat.card ↥(P ⊔ Subgroup.zpowers t) ≤ Nat.card ↥P := by
    rw [hn, ha]
    exact Nat.pow_le_pow_right (by norm_num) hna
  have hPeq : P = P ⊔ Subgroup.zpowers t :=
    Subgroup.eq_of_le_of_card_ge le_sup_left hcardle
  rw [hPeq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

end Work.CORE4
