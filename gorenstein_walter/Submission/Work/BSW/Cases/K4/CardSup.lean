/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 4` case)

# Elementary cardinality lemmas for subgroups

`|H ⊔ K| = |H| * |K|` when `K` normalizes `H` and `H ⊓ K = ⊥`; a subgroup of cardinality `1` is
trivial; subgroups of coprime cardinality intersect trivially; and `Q ⊔ D = N` follows from the
order formula when `Q, D ≤ N`, `D` normalizes `Q` and `|Q| * |D| = |N|`.
-/
import Mathlib
import Submission.Work.BSW.Concl

namespace Work.BSW.Cases.K4

open Subgroup Work.GW2

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

/-- If `K` normalizes `H` and `H ⊓ K = ⊥` then `|H ⊔ K| = |H| * |K|`. -/
theorem card_sup_of_le_normalizer_of_inf_eq_bot {H K : Subgroup G}
    (hN : K ≤ Subgroup.normalizer (H : Set G)) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  have hcoe : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H K hN
  have hbij : Function.Bijective
      (fun p : ↥H × ↥K =>
        (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(H ⊔ K))) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨h1, k1⟩ ⟨h2, k2⟩ heq
      simp only [Subtype.mk.injEq] at heq
      have h1' : (h2 : G)⁻¹ * (h1 : G) = (k2 : G) * (k1 : G)⁻¹ := by
        have := congrArg (fun z : G => (h2 : G)⁻¹ * z * (k1 : G)⁻¹) heq
        simpa [mul_assoc] using this
      have hbot : (h2 : G)⁻¹ * (h1 : G) ∈ (⊥ : Subgroup G) := by
        rw [← hd]
        exact ⟨H.mul_mem (H.inv_mem h2.2) h1.2,
          h1' ▸ K.mul_mem k2.2 (K.inv_mem k1.2)⟩
      have hh : (h2 : G)⁻¹ * (h1 : G) = 1 := Subgroup.mem_bot.mp hbot
      have hk : (k2 : G) * (k1 : G)⁻¹ = 1 := by rw [← h1']; exact hh
      exact Prod.ext (Subtype.ext (inv_mul_eq_one.mp hh).symm)
        (Subtype.ext (mul_inv_eq_one.mp hk).symm)
    · intro z
      have hz : (z : G) ∈ (H : Set G) * (K : Set G) := by
        rw [← hcoe]; exact z.2
      obtain ⟨h, hh, k, hk, hhk⟩ := Set.mem_mul.mp hz
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), by apply Subtype.ext; simpa using hhk⟩
  calc Nat.card ↥(H ⊔ K) = Nat.card (↥H × ↥K) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod _ _

/-- A subgroup of cardinality `1` is trivial. -/
theorem eq_bot_of_card_eq_one {H : Subgroup G} (h : Nat.card ↥H = 1) : H = ⊥ :=
  Subgroup.eq_bot_of_card_eq (H := H) h

/-- Subgroups of coprime cardinality intersect trivially. -/
theorem inf_eq_bot_of_coprime {H K : Subgroup G} (h : (Nat.card ↥H).Coprime (Nat.card ↥K)) :
    H ⊓ K = ⊥ := by
  refine eq_bot_of_card_eq_one ?_
  have h1 : Nat.card ↥(H ⊓ K) ∣ Nat.card ↥H := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(H ⊓ K) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le inf_le_right
  exact Nat.eq_one_of_dvd_one (h ▸ Nat.dvd_gcd h1 h2)

/-- `Q ⊔ D = N` when `Q, D ≤ N`, `D` normalizes `Q`, `Q ⊓ D = ⊥` and `|Q| * |D| = |N|`. -/
theorem sup_eq_of_card_mul_eq {Q D N : Subgroup G} (hQ : Q ≤ N) (hD : D ≤ N)
    (hN : D ≤ Subgroup.normalizer (Q : Set G)) (hd : Q ⊓ D = ⊥)
    (hcard : Nat.card ↥Q * Nat.card ↥D = Nat.card ↥N) :
    Q ⊔ D = N := by
  have hsub : Q ⊔ D ≤ N := sup_le hQ hD
  have hcard' : Nat.card ↥(Q ⊔ D) = Nat.card ↥N := by
    rw [card_sup_of_le_normalizer_of_inf_eq_bot hN hd, hcard]
  exact Subgroup.eq_of_le_of_card_ge hsub (le_of_eq hcard'.symm)

/-- If `H ≤ K` and `H` has index `2` in `K` (expressed as `2 * |H| = |K|`) then `K` normalizes
`H`. -/
theorem le_normalizer_of_two_mul_card {H K : Subgroup G} (hle : H ≤ K)
    (hcard : 2 * Nat.card ↥H = Nat.card ↥K) :
    K ≤ Subgroup.normalizer (H : Set G) := by
  have hcard' : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  have hidx : (H.subgroupOf K).index = 2 := by
    have hmul := Subgroup.card_mul_index (H.subgroupOf K)
    rw [hcard'] at hmul
    have h2 : Nat.card ↥H * (H.subgroupOf K).index = Nat.card ↥H * 2 := by
      calc Nat.card ↥H * (H.subgroupOf K).index = Nat.card ↥K := hmul
        _ = 2 * Nat.card ↥H := hcard.symm
        _ = Nat.card ↥H * 2 := by ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hnorm : (H.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two hidx
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hnorm

/-- A natural number divisible by `21` and by `7` is `7` or `21`. -/
theorem nat_eq_seven_or_twentyone {m : ℕ} (h1 : m ∣ 21) (h2 : 7 ∣ m) : m = 7 ∨ m = 21 := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hb3 : b * a = 3 := by
    have h' : 7 * (b * a) = 7 * 3 := by
      calc 7 * (b * a) = (7 * b) * a := by ring
        _ = m * a := by rw [← hb]
        _ = 21 := ha.symm
        _ = 7 * 3 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three b ⟨a, hb3.symm⟩ with h | h
  · exact Or.inl (by rw [hb, h, mul_one])
  · exact Or.inr (by rw [hb, h])

end Work.BSW.Cases.K4
