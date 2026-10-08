import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.q_structure
import Submission.Work.ZassenhausSuzuki.Odd.odd_centralizer_odd
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_basic
import Submission.Work.ZassenhausSuzuki.Odd.twoPoint_isCZ
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_hall
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_inf_conj
import Submission.Work.ZassenhausSuzuki.Odd.sum_card_sub_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Elementary consequences of `SzOddHyp`

The first block of helpers for `Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki`:
the order of `G`, the absence of elements of mixed order, and the size bounds for members of
`ℱ`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `|G| = q²(q-1)(q²+1)` for the Suzuki rank-one configuration. -/
theorem card_G_eq (h : SzOddHyp H Q t) :
    Nat.card G = q H ^ 2 * (q H - 1) * (q H ^ 2 + 1) := by
  obtain ⟨hQ2, hD, hq4, hpow, h3, hidx⟩ := q_structure h
  have hH : Nat.card ↥H = Nat.card ↥Q * Nat.card ↥(twoPoint H t) :=
    Work.ThmF.split_card_H h.hsplit
  have hG : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
  rw [← hG, hH, hQ2, hD, hidx]

/-- `3` does not divide `q`. -/
theorem three_not_dvd_q (h : SzOddHyp H Q t) : ¬ 3 ∣ q H := by
  obtain ⟨hQ2, hD, hq4, hpow, h3, hidx⟩ := q_structure h
  obtain ⟨l, hl⟩ := hpow
  rw [hl]
  intro hdvd
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd) (by norm_num)

/-- `3` does not divide `q² + 1`. -/
theorem three_not_dvd_q_sq_add_one (h : SzOddHyp H Q t) : ¬ 3 ∣ q H ^ 2 + 1 := by
  obtain ⟨hQ2, hD, hq4, hpow, h3, hidx⟩ := q_structure h
  have hq3 : ¬ 3 ∣ q H := three_not_dvd_q h
  intro hdvd
  have hmod : (q H ^ 2 + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hlt : q H % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hne : q H % 3 ≠ 0 := fun hc => hq3 (Nat.dvd_iff_mod_eq_zero.mpr hc)
  have hqmod : q H % 3 = 1 ∨ q H % 3 = 2 := by omega
  rcases hqmod with hc | hc <;>
    · rw [Nat.add_mod, Nat.pow_mod, hc] at hmod
      norm_num at hmod

/-- `3` does not divide `|G|`: `|G| = q²(q-1)(q²+1)` with `3 ∤ q`, `3 ∤ q²+1` and `3 ∤ q - 1`. -/
theorem three_not_dvd_card_G (h : SzOddHyp H Q t) : ¬ 3 ∣ Nat.card G := by
  obtain ⟨hQ2, hD, hq4, hpow, h3, hidx⟩ := q_structure h
  have hq3 : ¬ 3 ∣ q H := three_not_dvd_q h
  have hq23 : ¬ 3 ∣ q H ^ 2 := fun hc => hq3 (Nat.Prime.dvd_of_dvd_pow (by norm_num) hc)
  have hq21 : ¬ 3 ∣ q H ^ 2 + 1 := three_not_dvd_q_sq_add_one h
  rw [card_G_eq h]
  intro hdvd
  have h1 : 3 ∣ q H ^ 2 * ((q H - 1) * (q H ^ 2 + 1)) := by
    simpa [mul_assoc] using hdvd
  have h2 : 3 ∣ (q H - 1) * (q H ^ 2 + 1) := by
    rcases (Nat.prime_three.dvd_mul).mp h1 with hc | hc
    · exact absurd hc hq23
    · exact hc
  rcases (Nat.prime_three.dvd_mul).mp h2 with hc | hc
  · exact h3 hc
  · exact hq21 hc

/-- Every member of `ℱ` has order at least `5`: it is odd, `> 1` and divides `|G|`, which is
not divisible by `3`. -/
theorem isCZ_card_ge_five (h : SzOddHyp H Q t) {A : Subgroup G} (hA : IsCZ A) :
    5 ≤ Nat.card ↥A := by
  obtain ⟨-, hodd, -⟩ := isCZ_basic h hA
  obtain ⟨x, hx, hx1, -, hxA⟩ := hA
  have hdvd : Nat.card ↥A ∣ Nat.card G := by
    rw [← hxA]
    exact Subgroup.card_subgroup_dvd_card _
  have hne1 : Nat.card ↥A ≠ 1 := by
    intro hc
    have hsub : Subsingleton ↥A := (Nat.card_eq_one_iff_unique.mp hc).1
    have hxmem : x ∈ A := by
      rw [← hxA]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have h1 : (⟨x, hxmem⟩ : ↥A) = 1 := Subsingleton.elim _ _
    exact hx1 (Subtype.ext_iff.mp h1)
  have h3 : ¬ 3 ∣ Nat.card G := three_not_dvd_card_G h
  have h3A : ¬ 3 ∣ Nat.card ↥A := fun hc => h3 (hc.trans hdvd)
  have hne3 : Nat.card ↥A ≠ 3 := fun hc => h3A (hc ▸ dvd_rfl)
  obtain ⟨k, hk⟩ := hodd
  omega

/-- No element of `G` has mixed order: every non-identity element is either a `2`-element or of
odd order. -/
theorem no_mixed_order (h : SzOddHyp H Q t) {x : G} (hx1 : x ≠ 1) :
    PowTwoOrder x ∨ Odd (orderOf x) := by
  have hn0 : orderOf x ≠ 0 := by
    have := IsOfFinOrder.orderOf_pos (isOfFinOrder_of_finite x)
    omega
  obtain ⟨k, m, hm_odd, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hm0 : 0 < m := by
    rcases hm_odd with ⟨j, hj⟩
    omega
  have h2k0 : 0 < 2 ^ k := by positivity
  by_cases hm : m = 1
  · left
    exact ⟨k, by rw [hn, hm, mul_one]⟩
  · right
    have hgcd1 : (2 ^ k * m).gcd (2 ^ k) = 2 ^ k := by
      calc (2 ^ k * m).gcd (2 ^ k) = (2 ^ k * m).gcd (2 ^ k * 1) := by rw [mul_one]
        _ = 2 ^ k * (m.gcd 1) := Nat.gcd_mul_left _ _ _
        _ = 2 ^ k := by rw [Nat.gcd_one_right, mul_one]
    have hgcd2 : (2 ^ k * m).gcd m = m := by
      calc (2 ^ k * m).gcd m = (2 ^ k * m).gcd (1 * m) := by rw [one_mul]
        _ = (2 ^ k).gcd 1 * m := Nat.gcd_mul_right _ _ _
        _ = m := by rw [Nat.gcd_one_right, one_mul]
    have hz_ord : orderOf (x ^ 2 ^ k) = m := by
      rw [orderOf_pow, hn, hgcd1]
      exact Nat.mul_div_cancel_left m h2k0
    have hu_ord : orderOf (x ^ m) = 2 ^ k := by
      rw [orderOf_pow, hn, hgcd2]
      exact Nat.mul_div_left (2 ^ k) hm0
    have hz1 : x ^ 2 ^ k ≠ 1 := by
      intro hc
      rw [hc, orderOf_one] at hz_ord
      exact hm hz_ord.symm
    have hz_odd : Odd (orderOf (x ^ 2 ^ k)) := by rw [hz_ord]; exact hm_odd
    have hcent : Odd (Nat.card ↥(Subgroup.centralizer ({x ^ 2 ^ k} : Set G))) :=
      odd_centralizer_odd h hz1 hz_odd
    have hmem : x ^ m ∈ Subgroup.centralizer ({x ^ 2 ^ k} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Commute.pow_pow (Commute.refl x) m (2 ^ k)).eq
    have hdvd : orderOf (x ^ m) ∣ Nat.card ↥(Subgroup.centralizer ({x ^ 2 ^ k} : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hmem
    rw [hu_ord] at hdvd
    have h2k_odd : Odd (2 ^ k) := Odd.of_dvd_nat hcent hdvd
    have hk : k = 0 := by
      by_contra hk0
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have h2 : 2 ∣ 2 ^ (j + 1) := ⟨2 ^ j, by ring⟩
      exact (Nat.not_even_iff_odd.mpr h2k_odd) (even_iff_two_dvd.mpr h2)
    rw [hk, pow_zero, one_mul] at hn
    rw [hn]
    exact hm_odd

end Work.ZassenhausSuzuki.Odd
