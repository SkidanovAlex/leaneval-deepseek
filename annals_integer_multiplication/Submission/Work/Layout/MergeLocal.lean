import Mathlib
import Submission.Work.Layout.MergeDefs

set_option autoImplicit false

/-!
# The per-column arithmetic estimate for `cmpCost`

For a key `K` and a list `vs` of *distinct* naturals `< K`, the cost of the comparisons performed while
`K` is the head of one of the two lists is `|vs| * ((K.size).size)` (one read of the cached key size per
consumed element).  This file proves that this is bounded by
`9 * K.size + 9 * Σ_{v ∈ vs} v.size + 5 * |vs|`: the `Σ v.size` term measures the distinct consumed
elements, whose sizes grow at least like those of `0, 1, …, |vs|-1`.

The key ingredient is `two_mul_sum_ge`: a list of `a` distinct naturals has `2 * Σ v.size ≥ (a.size - 2) * a`,
proved by a counting argument (at most `2^j` distinct naturals have size `< j`).
-/

namespace Work.Layout

open HvdH

theorem length_le_of_nodup_lt (K : ℕ) (vs : List ℕ) (hnd : vs.Nodup) (hlt : ∀ v ∈ vs, v < K) :
    vs.length ≤ K := by
  have hsub : vs.toFinset ⊆ Finset.range K := by
    intro v hv
    rw [Finset.mem_range]
    exact hlt v (List.mem_toFinset.mp hv)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_range, List.toFinset_card_of_nodup hnd] at h1
  exact h1

theorem two_mul_sum_ge (vs : List ℕ) (hnd : vs.Nodup) :
    (vs.length.size - 2) * vs.length ≤ 2 * (vs.map (fun v => v.size)).sum := by
  set a := vs.length with ha
  set S := (vs.map (fun v => v.size)).sum with hS
  set A := a.size with hA
  rcases Nat.lt_or_ge A 3 with hA3 | hA3
  · have : A - 2 = 0 := by omega
    rw [this, Nat.zero_mul]
    omega
  · set j := A - 2 with hj
    set t := vs.toFinset with ht
    have hsmall : (t.filter (fun v => v.size < j)).card ≤ 2 ^ j := by
      have hsub : t.filter (fun v => v.size < j) ⊆ Finset.range (2 ^ j) := by
        intro v hv
        rw [Finset.mem_range]
        have h2 : v.size < j := (Finset.mem_filter.mp hv).2
        exact Nat.size_le.mp (by omega)
      calc (t.filter (fun v => v.size < j)).card ≤ (Finset.range (2 ^ j)).card :=
            Finset.card_le_card hsub
        _ = 2 ^ j := Finset.card_range _
    have h2 : (t.filter (fun v => ¬ j ≤ v.size)).card ≤ 2 ^ j := by
      have heq : t.filter (fun v => ¬ j ≤ v.size) = t.filter (fun v => v.size < j) :=
        Finset.filter_congr (fun v _ => not_le)
      rw [heq]
      exact hsmall
    have hcardadd : a ≤ (t.filter (fun v => j ≤ v.size)).card + 2 ^ j := by
      have h1 := Finset.card_filter_add_card_filter_not (s := t) (fun v => j ≤ v.size)
      have hcard : t.card = a := by rw [ht, ha, List.toFinset_card_of_nodup hnd]
      omega
    have hpowa : 2 ^ (j + 1) ≤ a := by
      have h1 : 2 ^ (a.size - 1) ≤ a := Nat.lt_size.mp (by omega)
      have h2 : j + 1 = a.size - 1 := by omega
      rw [h2]
      exact h1
    have hcardge : 2 ^ j ≤ (t.filter (fun v => j ≤ v.size)).card := by
      have h2j : 2 ^ (j + 1) = 2 ^ j * 2 := by rw [pow_succ]
      nlinarith [hpowa, hcardadd]
    have hsum : j * (t.filter (fun v => j ≤ v.size)).card ≤ S := by
      have h1 : (t.filter (fun v => j ≤ v.size)).card • j
          ≤ (t.filter (fun v => j ≤ v.size)).sum (fun v => v.size) :=
        Finset.card_nsmul_le_sum _ _ j (fun v hv => (Finset.mem_filter.mp hv).2)
      rw [nsmul_eq_mul] at h1
      have h2 : (t.filter (fun v => j ≤ v.size)).sum (fun v => v.size) ≤ t.sum (fun v => v.size) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => Nat.zero_le _)
      have h3 : t.sum (fun v => v.size) = S := by
        rw [ht, hS]
        exact List.sum_toFinset _ hnd
      calc j * (t.filter (fun v => j ≤ v.size)).card
          = (t.filter (fun v => j ≤ v.size)).card * j := Nat.mul_comm _ _
        _ ≤ (t.filter (fun v => j ≤ v.size)).sum (fun v => v.size) := h1
        _ ≤ t.sum (fun v => v.size) := h2
        _ = S := h3
    have h1 : j * a ≤ 2 * (j * (t.filter (fun v => j ≤ v.size)).card) := by
      nlinarith [hcardge, hcardadd]
    have h2 : 2 * (j * (t.filter (fun v => j ≤ v.size)).card) ≤ 2 * S := by
      nlinarith [hsum]
    have h3 : (A - 2) * a ≤ 2 * S := by
      rw [← hj]
      exact le_trans h1 h2
    exact h3

theorem mergeLocal (K : ℕ) (vs : List ℕ) (hnd : vs.Nodup) (hlt : ∀ v ∈ vs, v < K) :
    vs.length * ((K.size).size) ≤ 9 * K.size + 9 * (vs.map (fun v => v.size)).sum + 5 * vs.length := by
  set a := vs.length with ha
  set S := (vs.map (fun v => v.size)).sum with hS
  set A := a.size with hA
  set s := K.size with hs
  set b := s.size with hb
  have hS2 : (A - 2) * a ≤ 2 * S := by
    rw [hA, ha, hS]
    exact two_mul_sum_ge vs hnd
  have haK : a ≤ K := by rw [ha]; exact length_le_of_nodup_lt K vs hnd hlt
  have has : a < 2 ^ s := by
    have h2 : K < 2 ^ s := by rw [hs]; exact Nat.lt_size_self K
    exact lt_of_le_of_lt haK h2
  rcases Nat.lt_or_ge a 9 with h9 | h9
  · have hbs : b ≤ s := by rw [hb, hs]; exact size_le_self K.size
    have h1 : a * b ≤ 8 * s := by
      calc a * b ≤ 8 * b := Nat.mul_le_mul_right b (by omega)
        _ ≤ 8 * s := Nat.mul_le_mul_left 8 hbs
    have h2 : 8 * s ≤ 9 * s + 9 * S + 5 * a := by
      have := Nat.zero_le S
      omega
    exact le_trans h1 h2
  · have hs1 : 1 ≤ s := by
      rw [hs]
      exact Nat.size_pos.mpr (by omega)
    have hsge : 2 ^ (b - 1) ≤ s := by
      have hspos : 1 ≤ s.size := by
        have := Nat.size_pos.mpr (by omega : 0 < s)
        omega
      rw [hb]
      exact Nat.lt_size.mp (by omega)
    have ha2A : a < 2 ^ A := by rw [hA]; exact Nat.lt_size_self a
    have hA4 : 4 ≤ A := by
      rw [hA]
      have h1 : (9 : ℕ).size ≤ a.size := Nat.size_le_size h9
      have h2 : (9 : ℕ).size = 4 := by decide
      omega
    have hkey : 2 * (a * b) ≤ 18 * s + 9 * (A - 2) * a + 10 * a := by
      by_cases hc : 2 * b ≤ 9 * (A - 2) + 10
      · have h1 : 2 * (a * b) ≤ a * (9 * (A - 2) + 10) := by nlinarith [hc]
        nlinarith [h1]
      · push_neg at hc
        have hbA : A ≤ b := by omega
        have hle : 2 * b ≤ 9 * (A - 2) + 10 + 2 * (b - A) := by omega
        have hd2 : 2 * (b - A) ≤ 2 ^ (b - A + 2) := by
          have h := Nat.lt_two_pow_self (n := b - A)
          have he : (2:ℕ) ^ (b - A + 2) = 4 * 2 ^ (b - A) := by
            rw [show b - A + 2 = (b - A) + 2 from by omega, pow_add]
            ring
          omega
        have hpow : 2 ^ A * 2 ^ (b - A + 2) = 8 * 2 ^ (b - 1) := by
          rw [← pow_add]
          have hAb : A + (b - A + 2) = (b - 1) + 3 := by omega
          rw [hAb, pow_add]
          ring
        have hstep : 2 * (a * b) ≤ a * (9 * (A - 2) + 10 + 2 * (b - A)) := by
          nlinarith [hle]
        have h1 : a * (2 * (b - A)) ≤ 8 * s := by
          calc a * (2 * (b - A)) ≤ 2 ^ A * (2 * (b - A)) :=
                Nat.mul_le_mul_right _ (le_of_lt ha2A)
            _ ≤ 2 ^ A * 2 ^ (b - A + 2) := Nat.mul_le_mul_left _ hd2
            _ = 8 * 2 ^ (b - 1) := hpow
            _ ≤ 8 * s := Nat.mul_le_mul_left 8 hsge
        nlinarith [hstep, h1]
    have hfinal : 2 * (a * b) ≤ 2 * (9 * s + 9 * S + 5 * a) := by nlinarith [hS2, hkey]
    omega


end Work.Layout
