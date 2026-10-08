import Mathlib

set_option linter.style.haveILetI false

namespace Work.BSW.Cases.K4

/-- In a finite group `H` of order `24`, the normalizer of any subgroup `X ≤ H` of order `3`
has even order.  Since `|H| = 24 = 2³ · 3` and `|X| = 3`, `X` is a Sylow `3`-subgroup of `H`.
Writing `N = N_H(X)` and `n₃ = |Sylow 3 H| = [H : N]`, we have `|N| · n₃ = 24`, so `n₃ ∣ 24`,
and Sylow's congruence gives `n₃ ≡ 1 (mod 3)`.  The divisors of `24` congruent to `1` modulo `3`
are `1` and `4`, giving `|N| = 24` or `|N| = 6`; in either case `2 ∣ |N|`. -/
theorem two_dvd_card_normalizer_of_card_eq_three {H : Type} [Group H] [Finite H]
    (X : Subgroup H) (hH : Nat.card H = 24) (hX : Nat.card ↥X = 3) :
    2 ∣ Nat.card ↥(Subgroup.normalizer (X : Set H)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite (Sylow 3 H) := inferInstance
  -- `3` divides `|H| = 24` with multiplicity one, and `|X| = 3 = 3¹`, so `X` is a Sylow
  -- `3`-subgroup of `H`.
  have hfac : (Nat.card H).factorization 3 = 1 := by rw [hH]; norm_num [Nat.factorization]
  have hXcard : Nat.card ↥X = 3 ^ (Nat.card H).factorization 3 := by rw [hfac, pow_one, hX]
  let P : Sylow 3 H := Sylow.ofCard X hXcard
  have hP : (P : Subgroup H) = X := Sylow.coe_ofCard X hXcard
  have hmod : Nat.card (Sylow 3 H) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 H
  let N : Subgroup H := Subgroup.normalizer (X : Set H)
  change 2 ∣ Nat.card ↥N
  -- The number of Sylow `3`-subgroups is the index of the normalizer of any Sylow subgroup,
  -- in particular of `N = N_H(X)`.
  have hidx : Nat.card (Sylow 3 H) = N.index := by
    change Nat.card (Sylow 3 H) = (Subgroup.normalizer (X : Set H)).index
    rw [← hP]; exact Sylow.card_eq_index_normalizer P
  -- `|N| · [H : N] = |H|`.
  have hmul : Nat.card ↥N * N.index = 24 := by
    have := Subgroup.card_mul_index N
    rw [hH] at this; exact this
  have hndvd : N.index ∣ 24 := ⟨Nat.card ↥N, by rw [← hmul, mul_comm]⟩
  have hmodn : N.index ≡ 1 [MOD 3] := by rw [← hidx]; exact hmod
  have hnpos : 0 < N.index := Nat.pos_of_dvd_of_pos hndvd (by norm_num)
  have hnle : N.index ≤ 24 := Nat.le_of_dvd (by norm_num) hndvd
  -- The divisors of `24` congruent to `1` modulo `3` are `1` and `4`.
  have hn14 : N.index = 1 ∨ N.index = 4 := by
    interval_cases N.index <;> simp_all [Nat.ModEq]
  rcases hn14 with h | h
  · have : Nat.card ↥N = 24 := by rw [h, mul_one] at hmul; exact hmul
    rw [this]; norm_num
  · have : Nat.card ↥N = 6 := by rw [h] at hmul; omega
    rw [this]; norm_num

end Work.BSW.Cases.K4
