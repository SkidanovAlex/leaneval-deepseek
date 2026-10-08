import Mathlib

namespace Work.CORE4.DihFourConjAux

/-- If `W ≤ C_G(u)` is a `2`-subgroup and some Sylow `2`-subgroup of `G` lies in `C_G(u)`, then
some Sylow `2`-subgroup `R` of `G` satisfies `W ≤ R ≤ C_G(u)`. -/
theorem exists_sylow_le_centralizer {G : Type} [Group G] [Finite G]
    (W : Subgroup G) (hW : IsPGroup 2 W) (u : G)
    (hWcent : W ≤ Subgroup.centralizer ({u} : Set G))
    (hcent : ∃ T : Sylow 2 G, (T : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G)) :
    ∃ R : Sylow 2 G, W ≤ (R : Subgroup G) ∧
      (R : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := by
  classical
  -- Write `C` for the centralizer of `u`.
  let C : Subgroup G := Subgroup.centralizer ({u} : Set G)
  have hWC' : W ≤ C := hWcent
  -- Some Sylow `2`-subgroup `T` of `G` lies in `C`.
  obtain ⟨T, hTC⟩ := hcent
  have hTC' : (T : Subgroup G) ≤ C := hTC
  -- Hence `2 ^ n` divides `|C|`, where `2 ^ n` is the order of `T`.
  have hcardT : Nat.card (T : Subgroup G) = 2 ^ (Nat.card G).factorization 2 := by
    rw [Sylow.card_eq_multiplicity T]
  have hcardTsub : Nat.card ((T : Subgroup G).subgroupOf C) = Nat.card (T : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC').toEquiv
  have h2nC : 2 ^ (Nat.card G).factorization 2 ∣ Nat.card C := by
    rw [← hcardT, ← hcardTsub]
    exact Subgroup.card_subgroup_dvd_card ((T : Subgroup G).subgroupOf C)
  -- `|W|` is a power of `2` dividing `|C|`, hence dividing `|G|`.
  have hWsub : Nat.card (W.subgroupOf C) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC').toEquiv
  have hWdividesC : Nat.card W ∣ Nat.card C := by
    rw [← hWsub]
    exact Subgroup.card_subgroup_dvd_card (W.subgroupOf C)
  have hWdividesG : Nat.card W ∣ Nat.card G :=
    hWdividesC.trans (Subgroup.card_subgroup_dvd_card C)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW
  have hkn : k ≤ (Nat.card G).factorization 2 := by
    rw [hk] at hWdividesG
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos.ne')).mp hWdividesG
  have hWdvd : Nat.card W ∣ 2 ^ (Nat.card G).factorization 2 := by
    rw [hk]
    exact pow_dvd_pow 2 hkn
  -- Sylow's first theorem applied inside `C` produces a `2`-subgroup `K` of `G` with
  -- `|K| = 2 ^ n` and `W ≤ K ≤ C`; it is a Sylow `2`-subgroup of `G`.
  obtain ⟨K, hKcard, hWK, hKC⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hWdvd h2nC hWC'
  exact ⟨Sylow.ofCard K hKcard, hWK, hKC⟩

end Work.CORE4.DihFourConjAux
