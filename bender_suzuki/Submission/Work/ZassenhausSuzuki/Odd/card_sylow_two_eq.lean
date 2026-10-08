import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The number of Sylow `2`-subgroups in the Suzuki rank-one configuration

In the Suzuki configuration `H = Q ⋊ D` with `|Q| = q²` and `|G| = q²(q-1)(q²+1)`, the root
group `Q` is a Sylow `2`-subgroup of `G` (its index `(q-1)(q²+1)` is odd), its normaliser is
`H` (Feit's `N_G(M) = M ⋊ D`, `Work.ZassenhausTwoGroup.normalizer_Q_eq`), and the count of
Sylow `2`-subgroups is therefore `[G : N_G(Q)] = [G : H] = q² + 1`
(`Work.ThmG.rankOne_index`).

This is the `Sz(q)`-case value of the number of Sylow `2`-subgroups; the corresponding fact for
the model groups is `Nat.card (Sylow 2 (SzModel n)) = |SzField n| ^ 2 + 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

theorem card_sylow_two_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) :
    Nat.card (Sylow 2 G) = Work.ZassenhausSuzuki.Odd.q H ^ 2 + 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ2, _, hq4, hpow, _, hidx⟩ := q_structure h
  have hQne : Q ≠ ⊥ := Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split h.hsplit
  -- ## `Q` has odd index in `G`
  have hqpos : 0 < q H ^ 2 := by
    have h0 : 0 < q H := by omega
    positivity
  have hindex : Q.index = (q H - 1) * (q H ^ 2 + 1) := by
    have hmul : Nat.card ↥Q * Q.index = Nat.card G := Subgroup.card_mul_index Q
    rw [hQ2, card_G_eq h] at hmul
    rw [mul_assoc] at hmul
    exact Nat.mul_left_cancel hqpos hmul
  have hqeven : Even (q H) := by
    obtain ⟨l, hl⟩ := hpow
    rw [hl]
    refine even_iff_two_dvd.mpr (dvd_pow_self 2 ?_)
    rintro rfl
    rw [pow_zero] at hl
    omega
  have hodd : Odd Q.index := by
    rw [hindex]
    have h1 : Odd (q H - 1) := Nat.Even.sub_odd (by omega) hqeven odd_one
    have h2 : Odd (q H ^ 2 + 1) := by
      obtain ⟨k, hk⟩ := hqeven
      refine Even.add_one ?_
      exact ⟨2 * k ^ 2, by rw [hk]; ring⟩
    exact h1.mul h2
  have hnot : ¬ 2 ∣ Q.index := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  -- ## `Q` as a Sylow `2`-subgroup of `G`
  let P : Sylow 2 G := h.h2.toSylow hnot
  have hP : (P : Subgroup G) = Q := IsPGroup.toSylow_coe h.h2 hnot
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex P
  -- ## the count is `[G : N_G(Q)] = [G : H]`
  rw [Sylow.card_eq_index_normalizer P]
  have hN : Subgroup.normalizer ((P : Subgroup G) : Set G) = H := by
    rw [hP]
    exact Work.ZassenhausTwoGroup.normalizer_Q_eq h.hsplit hQne
  change (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = q H ^ 2 + 1
  rw [hN, hidx]

end Work.ZassenhausSuzuki.Odd
