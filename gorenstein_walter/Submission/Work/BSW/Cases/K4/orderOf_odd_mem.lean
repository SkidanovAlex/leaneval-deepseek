import Mathlib
import Submission.Work.BSW.Defs
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Cases.K4.Setup

namespace Work.BSW.Cases.K4

/-- In the `|K| = 4`, `|G| = 360`, `n₅ = 6` case of BSW, an element of odd order has order
`1`, `3`, `5`, `9` or `15`.

`m = orderOf x` divides `360 = 2³·3²·5` and is odd, so `m ∣ 45`, i.e. `m ∈ {1, 3, 5, 9, 15, 45}`.
Order `45` is impossible: `x⁹` has order `5`, so `P := ⟨x⁹⟩` is a Sylow `5`-subgroup of `G`,
`x ∈ C_G(P)`, hence `45 = orderOf x` divides `|C_G(P)|`, which divides
`|N_G(P)| = 360 / n₅ = 60`; but `45 ∤ 60`.  (`h5 : Nat.card (Sylow 5 G) = 6` gives
`|N_G(P)| = 60` via `Sylow.card_eq_index_normalizer` and `Subgroup.card_mul_index`.) -/
theorem orderOf_odd_mem {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hK4 : Nat.card ↥K = 4) (hG : Nat.card G = 360)
    (h5 : Nat.card (Sylow 5 G) = 6) (x : G) (hx : Odd (orderOf x)) :
    orderOf x = 1 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 9 ∨ orderOf x = 15 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  -- `m = orderOf x` divides `360` and is odd, hence divides `45 = 360 / 2³`.
  have hm_dvd360 : orderOf x ∣ 360 := by rw [← hG]; exact orderOf_dvd_natCard x
  have hm_cop2 : (orderOf x).Coprime 2 := Nat.coprime_two_right.mpr hx
  have hm_dvd45 : orderOf x ∣ 45 := by
    have h1 : orderOf x ∣ 8 * 45 := by
      rw [show 8 * 45 = 360 from by norm_num]; exact hm_dvd360
    exact (hm_cop2.pow_right 3).dvd_of_dvd_mul_left h1
  -- Order `45` is impossible: `⟨x⁹⟩` is a Sylow `5`-subgroup centralized by `x`, so
  -- `45 = orderOf x` divides `|C_G(⟨x⁹⟩)| ≤ |N_G(⟨x⁹⟩)| = 360 / 6 = 60`.
  have hm_ne45 : orderOf x ≠ 45 := by
    intro hm45
    have hy : orderOf (x ^ 9) = 5 := by rw [orderOf_pow, hm45]; norm_num
    have hcard : Nat.card ↥(Subgroup.zpowers (x ^ 9)) = 5 := by
      rw [Nat.card_zpowers, hy]
    have hp : IsPGroup 5 ↥(Subgroup.zpowers (x ^ 9)) :=
      IsPGroup.of_card (p := 5) (n := 1) (by rw [hcard]; norm_num)
    have hidx : ¬ 5 ∣ (Subgroup.zpowers (x ^ 9)).index := by
      have hmul := Subgroup.card_mul_index (Subgroup.zpowers (x ^ 9))
      rw [hcard, hG] at hmul
      rintro ⟨k, hk⟩
      omega
    let P : Sylow 5 G := hp.toSylow hidx
    have hcent : x ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
      have hPcoe : ((P : Subgroup G) : Set G) = ((Subgroup.zpowers (x ^ 9)) : Set G) := rfl
      rw [hPcoe, Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (((Commute.refl x).pow_right 9).zpow_right n).symm
    have hN : x ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ hcent
    have hdvd : orderOf x ∣ Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) :=
      orderOf_dvd_natCard_of_mem hN
    have hN60 : Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) = 60 := by
      have hidx2 : (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 6 := by
        have hh := Sylow.card_eq_index_normalizer P
        rw [h5] at hh
        exact hh.symm
      have hmul := Subgroup.card_mul_index (Subgroup.normalizer ((P : Subgroup G) : Set G))
      rw [hidx2, hG] at hmul
      omega
    rw [hN60, hm45] at hdvd
    norm_num at hdvd
  -- The divisors of `45` are `1, 3, 5, 9, 15, 45`; `45` is excluded, leaving four values.
  have hmem : orderOf x ∈ ({1, 3, 5, 9, 15, 45} : Finset ℕ) := by
    have h1 : orderOf x ∈ Nat.divisors 45 := Nat.mem_divisors.mpr ⟨hm_dvd45, by norm_num⟩
    have hd : Nat.divisors 45 = ({1, 3, 5, 9, 15, 45} : Finset ℕ) := by decide
    rwa [hd] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h3 | h5' | h9 | h15 | h45
  · exact Or.inl h1
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr (Or.inl h5'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h9)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h15)))
  · exact absurd h45 hm_ne45

end Work.BSW.Cases.K4
