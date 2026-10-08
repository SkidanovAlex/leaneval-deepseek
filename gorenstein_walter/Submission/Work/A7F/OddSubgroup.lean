/-
Area A7F of the Gorenstein--Walter project: the odd-order subgroup bound in `A₇` (Bender 1.8).

The main result is `Work.A7F.odd_subgroup_card_le_21`: every odd-order subgroup of `A₇` has order
at most `21`.  The argument is the orbit analysis of the action of an odd-order subgroup `X ≤ A₇`
on the seven points:

* the orbits of `X` have odd size, dividing `|X|`, and they partition `Fin 7`; hence either `X` is
  transitive or `X` has a fixed point (`Work.A7F.orbit_dichotomy`);
* if `X` fixes a point, then `X` lies in the point stabilizer of order `360`, so `|X| ∣ 45`; the
  only excluded value is `45`, and a group of order `45` contains an element of order `15`, which
  `S₇` does not have;
* if `X` is transitive, then `|X| = 7·|X_p|` with `|X_p| ∣ 45`; excluding `|X_p| = 15, 45` again
  leaves `|X_p| ∈ {5, 9}`, i.e. `|X| ∈ {35, 63}`, and those orders do not occur in `A₇`
  (`Work.A7F.no_odd_subgroup_card_35_63`).
-/
import Mathlib
import Submission.Work.A7F.Defs
import Submission.Work.A7F.orbit_dichotomy
import Submission.Work.A7F.card_point_stabilizer
import Submission.Work.A7F.no_order_fifteen_perm
import Submission.Work.A7F.order_fifteen_group
import Submission.Work.A7F.order_fifteen_of_card_fortyfive
import Submission.Work.A7F.no_odd_subgroup_card_35_63

open scoped MatrixGroups

namespace Work.A7F

open Subgroup

/-- An odd divisor of `360` divides `45`. -/
private lemma odd_dvd_of_dvd_360 {d : ℕ} (hodd : Odd d) (h : d ∣ 360) : d ∣ 45 := by
  have hcop : d.Coprime 8 := by
    have h2 : d.Coprime 2 := Nat.coprime_two_right.mpr hodd
    have h3 := h2.pow_right 3
    simpa using h3
  have h8 : d ∣ 8 * 45 := by norm_num [show (8:ℕ) * 45 = 360 from rfl]; exact h
  exact hcop.dvd_of_dvd_mul_left h8

/-- The divisors of `45`. -/
private lemma dvd_45_cases {d : ℕ} (h : d ∣ 45) :
    d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 9 ∨ d = 15 ∨ d = 45 := by
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : d ≤ 45 := Nat.le_of_dvd (by norm_num) h
  interval_cases d <;> norm_num at h <;> omega

/-- **Bender 1.8: every odd-order subgroup of `A₇` has order at most `21`.**

This is the fourth conjunct of `Work.GW2.A7ModelProp`. -/
theorem odd_subgroup_card_le_21 (X : Subgroup (alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card X)) : Nat.card X ≤ 21 := by
  have hdvd2520 : Nat.card X ∣ 2520 := by
    have h := Subgroup.card_subgroup_dvd_card X
    rwa [nat_card_alternatingGroup_fin_seven] at h
  rcases orbit_dichotomy X hodd with hfix | htrans
  · -- `X` has a fixed point `p`: then `X` lies in the point stabilizer of order `360`.
    obtain ⟨p, hp⟩ := hfix
    have hle : X ≤ MulAction.stabilizer (alternatingGroup (Fin 7)) p := by
      intro x hx
      rw [MulAction.mem_stabilizer_iff]
      exact hp x hx
    have hdvd360 : Nat.card X ∣ 360 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [card_point_stabilizer p] at h
    have hdvd45 : Nat.card X ∣ 45 := odd_dvd_of_dvd_360 hodd hdvd360
    by_contra hgt
    push Not at hgt
    -- `|X| ∣ 45` and `21 < |X|` force `|X| = 45`, which is impossible.
    have h45 : Nat.card X = 45 := by
      obtain ⟨k, hk⟩ := hdvd45
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk
          omega
        · exact h
      have hk2 : k ≤ 2 := by
        have h1 : 22 * k ≤ Nat.card X * k := Nat.mul_le_mul_right k (by omega)
        rw [← hk] at h1
        omega
      interval_cases k <;> omega
    obtain ⟨g, hg⟩ := order_fifteen_of_card_fortyfive ↥X h45
    have h15 : 15 ∣ orderOf (((g : alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hg
    exact no_order_fifteen_perm _ h15
  · -- `X` is transitive on the seven points: `|X| = 7 * |X_p|`.
    set p₀ : Fin 7 := 0
    have horbit : MulAction.orbit X p₀ = Set.univ := by
      ext q
      constructor
      · intro _; trivial
      · intro _
        obtain ⟨x, hx, hxq⟩ := htrans p₀ q
        exact ⟨⟨x, hx⟩, hxq⟩
    have hcard : Nat.card X = 7 * Nat.card (MulAction.stabilizer X p₀) := by
      have hidx : (MulAction.stabilizer X p₀).index = 7 := by
        rw [MulAction.index_stabilizer X p₀, horbit, Set.ncard_univ, Nat.card_fin]
      have h := Subgroup.card_mul_index (MulAction.stabilizer X p₀)
      rw [hidx] at h
      omega
    have hs_odd : Odd (Nat.card (MulAction.stabilizer X p₀)) := by
      rw [hcard] at hodd
      exact Nat.Odd.of_mul_right hodd
    have hs_dvd : Nat.card (MulAction.stabilizer X p₀) ∣ 45 := by
      have hmap : (MulAction.stabilizer X p₀).map X.subtype ≤
          MulAction.stabilizer (alternatingGroup (Fin 7)) p₀ := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        rw [MulAction.mem_stabilizer_iff] at hx ⊢
        exact hx
      have hdvd360 : Nat.card (MulAction.stabilizer X p₀) ∣ 360 := by
        rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective X)]
        exact (Subgroup.card_dvd_of_le hmap).trans (by rw [card_point_stabilizer p₀])
      exact odd_dvd_of_dvd_360 hs_odd hdvd360
    have hs_le : Nat.card (MulAction.stabilizer X p₀) ≤ 3 := by
      rcases dvd_45_cases hs_dvd with h1 | h3 | h5 | h9 | h15 | h45
      · omega
      · omega
      · exfalso
        exact (no_odd_subgroup_card_35_63 X hodd).1 (by rw [hcard, h5])
      · exfalso
        exact (no_odd_subgroup_card_35_63 X hodd).2 (by rw [hcard, h9])
      · exfalso
        obtain ⟨g, hg⟩ := order_fifteen_group ↥(MulAction.stabilizer X p₀) h15
        have h15' : 15 ∣ orderOf ((((g : ↥(MulAction.stabilizer X p₀)) : ↥X) :
            alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
          rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
        exact no_order_fifteen_perm _ h15'
      · exfalso
        obtain ⟨g, hg⟩ := order_fifteen_of_card_fortyfive ↥(MulAction.stabilizer X p₀) h45
        have h15' : 15 ∣ orderOf ((((g : ↥(MulAction.stabilizer X p₀)) : ↥X) :
            alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
          rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
          exact hg
        exact no_order_fifteen_perm _ h15'
    calc Nat.card X = 7 * Nat.card (MulAction.stabilizer X p₀) := hcard
      _ ≤ 7 * 3 := by omega
      _ = 21 := by norm_num

end Work.A7F
