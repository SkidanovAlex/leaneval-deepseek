import Mathlib

set_option linter.style.haveILetI false

namespace Work.BSW.Cases

/-- For a finite simple group `G` of order `60`, a Sylow `5`-subgroup `P` has order `5`
and its normalizer has order `10`.

The Sylow count `n₅` divides `|G| : |P| = 60/5 = 12` and satisfies `n₅ ≡ 1 (mod 5)`, so
`n₅ ∈ {1, 6}`; `n₅ ≠ 1` by simplicity (a normal Sylow `5`-subgroup would be `⊥` or `⊤`,
neither possible), whence `n₅ = 6 = |G : N_G(P)|` and `|N_G(P)| = 60/6 = 10`. -/
theorem bswK2SylowFive {G : Type} [Group G] [Finite G] (hS : IsSimpleGroup G)
    (h60 : Nat.card G = 60) (P : Sylow 5 G) :
    Nat.card ↥(P : Subgroup G) = 5 ∧
      Nat.card ↥(Subgroup.normalizer (P : Set G)) = 10 := by
  haveI hp5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hne : Nonempty (Sylow 5 G) := ⟨P⟩
  -- The order of a Sylow `5`-subgroup is `5 ^ v₅(60) = 5`.
  have hPcard : Nat.card ↥(P : Subgroup G) = 5 := by
    rw [Sylow.card_eq_multiplicity, h60]
    have h1 : 1 ≤ (60 : ℕ).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five (by norm_num)).mp (by norm_num)
    have h2 : (60 : ℕ).factorization 5 < 2 := by
      by_contra h
      have hd : 5 ^ 2 ∣ (60 : ℕ) :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five (by norm_num)).mpr (by omega)
      norm_num at hd
    have : (60 : ℕ).factorization 5 = 1 := by omega
    rw [this]; norm_num
  refine ⟨hPcard, ?_⟩
  -- There is more than one Sylow `5`-subgroup: otherwise it would be normal.
  have hne1 : Nat.card (Sylow 5 G) ≠ 1 := by
    intro h1
    haveI : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hnrm : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    haveI := hnrm
    rcases hS.eq_bot_or_eq_top_of_normal (P : Subgroup G) with h | h
    · rw [h, Subgroup.card_bot] at hPcard; omega
    · rw [h, Subgroup.card_top] at hPcard; omega
  -- Now count: `n₅ ∣ 12` and `n₅ ≡ 1 (mod 5)` force `n₅ = 6`.
  have hn6 : Nat.card (Sylow 5 G) = 6 := by
    have hmod' : Nat.card (Sylow 5 G) % 5 = 1 := by
      have h := card_sylow_modEq_one 5 G
      rw [Nat.ModEq] at h
      simpa using h
    have hdvd12 : Nat.card (Sylow 5 G) ∣ 12 := by
      have hix : (P : Subgroup G).index = 12 := by
        have hmul := (P : Subgroup G).index_mul_card
        rw [hPcard, h60] at hmul
        omega
      have hcd := P.card_dvd_index
      rw [hix] at hcd
      exact hcd
    have hmem : Nat.card (Sylow 5 G) ∈ (12).divisors :=
      Nat.mem_divisors.mpr ⟨hdvd12, by norm_num⟩
    have hset : (12).divisors = {1, 2, 3, 4, 6, 12} := by decide
    rw [hset] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h
    · exact absurd h hne1
    · rw [h] at hmod'; norm_num at hmod'
    · rw [h] at hmod'; norm_num at hmod'
    · rw [h] at hmod'; norm_num at hmod'
    · exact h
    · rw [h] at hmod'; norm_num at hmod'
  have hidx : (Subgroup.normalizer (P : Set G)).index = 6 := by
    have h := P.card_eq_index_normalizer
    rw [hn6] at h
    exact h.symm
  have hmul := (Subgroup.normalizer (P : Set G)).index_mul_card
  rw [hidx, h60] at hmul
  omega

end Work.BSW.Cases
