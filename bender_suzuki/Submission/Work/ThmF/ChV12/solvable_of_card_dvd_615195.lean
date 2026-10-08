import Mathlib
import Submission.Work.ThmF.ChV12.solvable_of_card_dvd_two_pow_six_odd_no_five
import Submission.Work.ThmF.ChV12.sylow_normalizer_le_centralizer_of_card_prime
import Submission.Work.NPC.Engine

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Solvability of odd-order groups of order dividing `615195`

`615195 = 3 ^ 4 * 5 * 7 ^ 2 * 31 = 5 * 123039`.  The main theorem of this file states that every
finite group of odd order whose order divides `615195` is solvable.

The argument is a case split on whether `5` divides the order.

* If `5 ∤ |D|`, then `|D|` divides `3 ^ 4 * 7 ^ 2 * 31`, which is handled by the already proved
  `Work.ThmF.ChV12.solvable_of_card_dvd_123039` (via the wrapper
  `Work.ThmF.ChV12.solvable_of_card_dvd_two_pow_six_odd_no_five`, since `615195 ∣ 2 ^ 15 * 615195 =
  20158709760`).
* If `5 ∣ |D|`, the Sylow `5`-subgroup `P` has order exactly `5` (as `25 ∤ 615195`), so it is
  cyclic of prime order and `Aut(P) ≅ C₄`.  Since `|D|` is odd, `4` is coprime to `|D|`, and
  `N_D(P)/C_D(P) ↪ Aut(P)` together with `[N_D(P) : C_D(P)] ∣ |D|` forces `N_D(P) ≤ C_D(P)`
  (`Work.ThmF.ChV12.sylow_normalizer_le_centralizer_of_card_prime`).  Burnside's normal
  `p`-complement theorem (`Work.NPC.burnside_npc`) then gives a normal `5`-complement `N ⊴ D` of
  odd order, and `N` still has order dividing `20158709760` and coprime to `5`, so it is solvable by
  `Work.ThmF.ChV12.solvable_of_card_dvd_two_pow_six_odd_no_five`; the quotient `D ⧸ N` is a
  `5`-group, hence nilpotent, hence solvable; an extension of solvable groups is solvable.
-/

namespace Work.ThmF.ChV12

/-- `615195 = 5 * 3 ^ 4 * 7 ^ 2 * 31` divides `20158709760 = 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31`. -/
lemma dvd_20158709760_of_dvd_615195 {n : ℕ} (h : n ∣ 615195) : n ∣ 20158709760 :=
  h.trans (by norm_num)

theorem solvable_of_card_dvd_615195 {D : Type} [Group D] [Finite D]
    (hodd : Odd (Nat.card D)) (hcard : Nat.card D ∣ 615195) : Group.IsSolvable D := by
  have hDvd : Nat.card D ∣ 20158709760 := dvd_20158709760_of_dvd_615195 hcard
  by_cases h5 : 5 ∣ Nat.card D
  · -- ## The case `5 ∣ |D|`
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h25 : ¬ 25 ∣ Nat.card D := fun h => absurd (dvd_trans h hDvd) (by norm_num)
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 D))
    -- `P` has order exactly `5`
    have hPcard : Nat.card (P : Subgroup D) = 5 := by
      obtain ⟨k, hk5⟩ := (IsPGroup.iff_card.mp P.isPGroup')
      have hdvd : 5 ^ k ∣ Nat.card D := hk5 ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup D)
      have hcardmul : Nat.card (P : Subgroup D) * (P : Subgroup D).index = Nat.card D :=
        Subgroup.card_mul_index _
      have hk_le : k ≤ 1 := by
        by_contra h
        have h2k : 2 ≤ k := by omega
        exact h25 (by
          have hdvd' : 5 ^ 2 ∣ Nat.card D := dvd_trans (pow_dvd_pow 5 h2k) hdvd
          rw [show (25 : ℕ) = 5 ^ 2 from by norm_num]
          exact hdvd')
      have hk_ge : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · exfalso
          have hP1 : Nat.card (P : Subgroup D) = 1 := by rw [hk5, h0, pow_zero]
          have hidx : Nat.card D = (P : Subgroup D).index := by
            rw [← hcardmul, hP1, one_mul]
          exact P.not_dvd_index (hidx ▸ h5)
        · exact hpos
      rw [hk5, show k = 1 from le_antisymm hk_le hk_ge, pow_one]
    -- `4` is coprime to the odd number `|D|`
    have hcop : Nat.Coprime (5 - 1) (Nat.card D) := by
      have h2 : Nat.Coprime 2 (Nat.card D) := (Nat.coprime_two_right.mpr hodd).symm
      have h4 : Nat.Coprime 4 (Nat.card D) := by simpa using h2.pow_left 2
      simpa using h4
    have hNC : Subgroup.normalizer (P : Set D) ≤ Subgroup.centralizer (P : Set D) :=
      sylow_normalizer_le_centralizer_of_card_prime P hPcard hcop
    -- Burnside's normal `5`-complement theorem
    obtain ⟨N, hN⟩ := Work.NPC.burnside_npc P hNC
    haveI hNnormal : N.Normal := hN.normal
    have hNcop5 : ¬ 5 ∣ Nat.card ↥N := by
      intro hdvd
      have hg : (Nat.card ↥N).gcd 5 = 1 := hN.coprime_card
      have hgcd : 5 ∣ (Nat.card ↥N).gcd 5 := Nat.dvd_gcd hdvd (dvd_refl 5)
      rw [hg] at hgcd
      exact absurd hgcd (by norm_num)
    have hNodd : Odd (Nat.card ↥N) := by
      refine Nat.not_even_iff_odd.mp fun he => ?_
      have h2 : ¬ Even (Nat.card D) := Nat.not_even_iff_odd.mpr hodd
      exact h2 (he.trans_dvd (Subgroup.card_subgroup_dvd_card N))
    have hNdvd : Nat.card ↥N ∣ 20158709760 :=
      (Subgroup.card_subgroup_dvd_card N).trans hDvd
    haveI : Group.IsSolvable ↥N :=
      solvable_of_card_dvd_two_pow_six_odd_no_five hNodd hNdvd hNcop5
    -- the quotient `D ⧸ N` is a `5`-group, hence nilpotent, hence solvable
    haveI : Group.IsNilpotent (D ⧸ N) := hN.isPGroup_quotient.isNilpotent
    exact Group.isSolvable_of_subgroup_quotient N
  · -- ## The case `5 ∤ |D|`
    exact solvable_of_card_dvd_two_pow_six_odd_no_five hodd hDvd h5

end Work.ThmF.ChV12
