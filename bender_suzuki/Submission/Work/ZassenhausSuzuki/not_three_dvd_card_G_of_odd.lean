import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.structPair_sq
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ZassenhausSuzuki.SzA.ncard_orderOf_eq_two
import Submission.Work.ThmG.rankOne_index
import Submission.Work.ThmF.ChV12.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `3 ∤ |G|` for a Zassenhaus split rank-one configuration with root group `A(GF(2^m), θ)`

`three_not_dvd_card_G_aux` (`structPair_sq.lean`) proves `¬ 3 ∣ Nat.card G` for a split rank-one
Zassenhaus configuration `H = Q ⋊ D` whose root group is coordinatised by Higman's group
`A(K,θ)` over a field `K` of characteristic two, **assuming** `θ` is a Tits endomorphism
(`IsTitsTheta θ`, i.e. `θ² = (·)²`), which is used only to exclude `3 ∣ |K| - 1`.

Here we replace that hypothesis by the concrete statement that the field is `K = GF(2^m)` with
`m` **odd**.  Then `|K| = 2^m ≡ -1 (mod 3)`, so `3 ∤ |K| - 1` by elementary arithmetic, and the
rest of the argument is unchanged:

* `|Q| = |K|² = 2 ^ (2m)` (from `e : Q ≃* A(K,θ)`),
* `|D| = |K| - 1 = 2^m - 1` (`twoPoint_card_eq_involutions` + `SzA.ncard_orderOf_eq_two`;
  this count is independent of `θ`),
* `|G| = |H| · [G : H] = (|Q| · |D|) · (|Q| + 1)`
  (`Work.ThmF.card_H_eq_mul_of_data` and `Work.ThmG.rankOne_index`),
* `3 ∤ |Q|` (a power of `2`), `3 ∤ |Q| + 1` (no square is `-1` modulo `3`) and `3 ∤ |D|`
  (odd `m`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- No square in `ZMod 3` is `-1`. -/
private lemma zmod3_sq_add_one_ne_zero : ∀ x : ZMod 3, x * x + 1 ≠ 0 := by decide

/-- `3` does not divide `q ^ 2 + 1` for any natural number `q`. -/
private lemma three_not_dvd_sq_add_one (q : ℕ) : ¬ 3 ∣ q * q + 1 := by
  intro h
  have h1 : ((q * q + 1 : ℕ) : ZMod 3) = 0 := by
    have h' : (3 : ℤ) ∣ ((q * q + 1 : ℕ) : ℤ) := by exact_mod_cast h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q * q + 1 : ℕ) : ℤ) 3).mpr h'
    simpa using this
  push_cast at h1
  exact zmod3_sq_add_one_ne_zero (q : ZMod 3) h1

/-- For odd `m`, `3` does not divide `2 ^ m - 1`. -/
private lemma three_not_dvd_two_pow_sub_one {m : ℕ} (hm : Odd m) : ¬ 3 ∣ 2 ^ m - 1 := by
  intro h
  have h1 : ((2 ^ m - 1 : ℕ) : ZMod 3) = 0 := by
    have h' : (3 : ℤ) ∣ ((2 ^ m - 1 : ℕ) : ℤ) := by exact_mod_cast h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 ^ m - 1 : ℕ) : ℤ) 3).mpr h'
    simpa using this
  rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h1
  have h2 : (2 : ZMod 3) ^ m = 1 := sub_eq_zero.mp h1
  have h3 : (2 : ZMod 3) ^ m = -1 := by
    have hc : (2 : ZMod 3) = -1 := by decide
    rw [hc]
    exact hm.neg_one_pow
  rw [h2] at h3
  exact absurd h3 (by decide)

theorem not_three_dvd_card_G_of_odd {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} (hm : Odd m) {θ : GaloisField 2 m ≃+* GaloisField 2 m}
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ} :
    ¬ 3 ∣ Nat.card G := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hQfin : Finite ↥Q := Subtype.finite
  haveI hSzAfin : Finite (SzA (GaloisField 2 m) θ) :=
    Finite.of_injective e.symm e.symm.injective
  have hm0 : m ≠ 0 := hm.pos.ne'
  -- `|K| = 2 ^ m`
  have hKcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm0
  -- `|Q| = |K| ^ 2`
  have hQcard : Nat.card Q = Nat.card (GaloisField 2 m) * Nat.card (GaloisField 2 m) :=
    (Nat.card_congr e.toEquiv).trans (natCard_szA θ)
  -- `|D| = |K| - 1` (the count of the involutions of `A(K,θ)`, independent of `θ`)
  have hDcard : Nat.card ↥(twoPoint H t) = Nat.card (GaloisField 2 m) - 1 := by
    rw [twoPoint_card_eq_involutions hsplit hzass h2]
    rw [show (involutions (Q : Set G)) = {x : G | x ∈ Q ∧ orderOf x = 2} from rfl]
    rw [ncard_involutions_of_mulEquiv (Q := Q) e]
    exact SzA.ncard_orderOf_eq_two θ
  -- `|G| = (|Q| + 1) · |Q| · (|K| - 1)`
  have hGcard : Nat.card G =
      (Nat.card Q + 1) * Nat.card Q * (Nat.card (GaloisField 2 m) - 1) := by
    calc Nat.card G = Nat.card ↥H * H.index := (Subgroup.card_mul_index H).symm
      _ = (Nat.card Q * (Nat.card (GaloisField 2 m) - 1)) * (Nat.card Q + 1) := by
            rw [Work.ThmF.card_H_eq_mul_of_data (Work.ThmF.IsSplitRankOne.toData hsplit),
              hDcard, Work.ThmG.rankOne_index hsplit]
      _ = (Nat.card Q + 1) * Nat.card Q * (Nat.card (GaloisField 2 m) - 1) := by
            rw [Nat.mul_comm (Nat.card Q * (Nat.card (GaloisField 2 m) - 1))
                (Nat.card Q + 1),
              Nat.mul_assoc]
  -- `3` divides none of the three factors
  have h3Q : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := isPGroup_iff_card_dvd_pow.mp h2
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow (h3.trans hk)) (by norm_num)
  have h3Q1 : ¬ 3 ∣ Nat.card Q + 1 := by
    rw [hQcard]
    exact three_not_dvd_sq_add_one (Nat.card (GaloisField 2 m))
  have h3D : ¬ 3 ∣ Nat.card (GaloisField 2 m) - 1 := by
    rw [hKcard]
    exact three_not_dvd_two_pow_sub_one hm
  -- combine
  intro h3
  rw [hGcard] at h3
  rcases Nat.prime_three.dvd_mul.mp h3 with h | h
  · rcases Nat.prime_three.dvd_mul.mp h with h' | h'
    · exact h3Q1 h'
    · exact h3Q h'
  · exact h3D h

end Work.ZassenhausSuzuki
