import Mathlib

set_option linter.style.haveILetI false

namespace Work.BSW.Cases.K4

/-- In a finite simple group of order `168` the normalizer of a Sylow `7`-subgroup has order `21`
(equivalently: `n₇ = 8`).  `n₇ ≡ 1 (mod 7)` and `n₇ ∣ 24` give `n₇ ∈ {1, 8}`, and `n₇ ≠ 1` by
simplicity. -/
theorem card_normalizer_sylow_seven {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 168) (Q : Sylow 7 G) :
    Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) = 21 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  -- A Sylow `7`-subgroup has order `7 = 7 ^ 1`, since `7 ^ 2 = 49 ∤ 168`.
  have hcardQ : Nat.card (Q : Subgroup G) = 7 := by
    rw [Sylow.card_eq_multiplicity Q, hG]
    norm_num [Nat.factorization]
  -- Hence its index in `G` is `168 / 7 = 24`.
  have hindexQ : (Q : Subgroup G).index = 24 := by
    rw [Subgroup.index_eq_card_div, hcardQ, hG]
  -- `n₇` divides the index of any Sylow `7`-subgroup, hence divides `24`.
  have hdvd : Nat.card (Sylow 7 G) ∣ 24 := by
    rw [← hindexQ]
    exact Sylow.card_dvd_index Q
  -- Sylow's congruence theorem: `n₇ ≡ 1 (mod 7)`.
  have hmod : Nat.card (Sylow 7 G) % 7 = 1 := by
    have h := card_sylow_modEq_one 7 G
    rw [Nat.ModEq] at h
    omega
  -- `n₇ ≠ 1`, since a unique Sylow subgroup is normal, and a nontrivial proper normal
  -- subgroup cannot exist in a simple group.
  have hne1 : Nat.card (Sylow 7 G) ≠ 1 := by
    intro h1
    haveI : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hnormal : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
    haveI : (Q : Subgroup G).Normal := hnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top (Q : Subgroup G) with h | h
    · rw [h, Subgroup.card_bot] at hcardQ
      norm_num at hcardQ
    · rw [h, Subgroup.card_top, hG] at hcardQ
      norm_num at hcardQ
  -- Therefore `n₇ ∈ {1, 8}` collapses to `n₇ = 8`.
  have hn8 : Nat.card (Sylow 7 G) = 8 := by
    set n := Nat.card (Sylow 7 G) with hn
    have hge : 1 ≤ n := by omega
    have hle : n ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n <;> norm_num at *
  -- The number of Sylow subgroups is the index of the normalizer.
  have hidxN : (Subgroup.normalizer ((Q : Subgroup G) : Set G)).index = 8 :=
    (Sylow.card_eq_index_normalizer Q).symm.trans hn8
  -- `|G| = [G : N(Q)] * |N(Q)|`.
  have hmul := Subgroup.card_mul_index (Subgroup.normalizer ((Q : Subgroup G) : Set G))
  rw [hG, hidxN] at hmul
  omega

end Work.BSW.Cases.K4
