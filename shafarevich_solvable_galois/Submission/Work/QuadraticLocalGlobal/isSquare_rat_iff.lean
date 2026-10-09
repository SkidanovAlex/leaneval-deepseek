/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A rational number is a square iff it is positive and all `p`-adic valuations are even

`isSquare_rat_iff` characterises the squares of `ℚ` among the units: `x : ℚˣ` is a square
(rather, its image in `ℚ` is) if and only if `x > 0` and `v_p(x)` is even for every prime `p`.

The forward implication is immediate from the multiplicativity of `v_p`.  For the converse we
write `x = A · s²` with `A` a squarefree integer (`exists_squarefree_rep`); then `v_p(x)` and
`v_p(A)` have the same parity, so `v_p(A)` is even for every prime, whence `A.natAbs = 1`
(because `v_p(A) = 1 \neq 2ℤ` for every prime `p ∣ A.natAbs`, `padicVal_intUnit_eq_one_of_squarefree`),
and positivity forces `A = 1`.  Thus `x = s²` is a square.
-/
import Mathlib
import Submission.Work.QuadraticLocalGlobal.Defs
import Submission.Work.QuadraticLocalGlobal.exists_squarefree_rep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

/-- The `p`-adic valuation of a squarefree integer at a prime dividing it is `1`:
`A.natAbs` squarefree and `p ∣ A.natAbs` give `p ∣ A` but `p² ∤ A`. -/
private lemma padicVal_intUnit_eq_one_of_squarefree (A : ℤ) (hA : A ≠ 0)
    (hsq : Squarefree A.natAbs) (p : ℕ) [Fact p.Prime] (hpA : p ∣ A.natAbs) :
    padicVal p (intUnit A hA) = 1 := by
  have hAnz : A.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hA
  have hnotdvd : ¬ p ^ 2 ∣ A.natAbs := by
    have hh := (Nat.squarefree_iff_prime_squarefree.mp hsq) p (Fact.out : p.Prime)
    simpa [pow_two] using hh
  have h1 : 1 ≤ padicValNat p A.natAbs := one_le_padicValNat_of_dvd hAnz hpA
  have h2 : ¬ 2 ≤ padicValNat p A.natAbs :=
    fun h => hnotdvd ((padicValNat_dvd_iff_le (a := A.natAbs) (n := 2) hAnz).mpr h)
  have hval : padicValNat p A.natAbs = 1 := by omega
  have hcast : (padicValInt p A : ℤ) = 1 := by simp [padicValInt, hval]
  rw [padicVal, intUnit_coe, padicValRat.of_int, hcast]

/-- `v_p(a²) = 2 v_p(a)`. -/
private lemma padicVal_sq (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    padicVal p (a ^ 2) = 2 * padicVal p a := by
  rw [sq, padicVal_mul]
  ring

theorem isSquare_rat_iff (x : ℚˣ) : IsSquare ((x : ℚ)) ↔ 0 < (x : ℚ) ∧ ∀ p : ℕ, p.Prime → Even (Work.HilbertSymbol.padicVal p x) := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by simpa using hy)
    refine ⟨?_, ?_⟩
    · rw [hy]
      exact mul_self_pos.mpr hy0
    · intro p hp
      haveI : Fact p.Prime := ⟨hp⟩
      refine ⟨padicVal p (Units.mk0 y hy0), ?_⟩
      have hxu : x = Units.mk0 y hy0 * Units.mk0 y hy0 := by
        apply Units.ext
        simp only [Units.val_mul, Units.val_mk0]
        exact hy
      rw [hxu, padicVal_mul]
  · rintro ⟨hpos, hv⟩
    obtain ⟨A, hA, s, hsq, hAs, _⟩ := exists_squarefree_rep x
    have hxval : (x : ℚ) = (A : ℚ) * (s : ℚ) ^ 2 := by
      have h := congrArg (fun u : ℚˣ => (u : ℚ)) hAs
      simpa only [Units.val_mul, Units.val_pow_eq_pow_val, intUnit_coe] using h.symm
    have hAeven : ∀ p : ℕ, p.Prime → Even (padicVal p (intUnit A hA)) := by
      intro p hp
      haveI : Fact p.Prime := ⟨hp⟩
      have hx : padicVal p x = padicVal p (intUnit A hA) + 2 * padicVal p s := by
        rw [← hAs, padicVal_mul, padicVal_sq]
      have h2 : Even (2 * padicVal p s) := ⟨padicVal p s, by ring⟩
      have hsub : Even (padicVal p x - 2 * padicVal p s) := (hv p hp).sub h2
      rwa [hx, add_sub_cancel_right] at hsub
    have hnoPrime : ∀ p : ℕ, p.Prime → ¬ p ∣ A.natAbs := by
      intro p hp hpdiv
      haveI : Fact p.Prime := ⟨hp⟩
      have h1 : padicVal p (intUnit A hA) = 1 :=
        padicVal_intUnit_eq_one_of_squarefree A hA hsq p hpdiv
      have hodd := hAeven p hp
      rw [h1] at hodd
      exact absurd hodd (by decide)
    have hAabs1 : A.natAbs = 1 := by
      rcases Nat.eq_zero_or_pos A.natAbs with h | h
      · exact absurd h (Int.natAbs_ne_zero.mpr hA)
      · by_contra hne
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        exact hnoPrime p hp hpdvd
    have hApos : 0 < A := by
      have hs2 : 0 < (s : ℚ) ^ 2 :=
        sq_pos_of_ne_zero (show (s : ℚ) ≠ 0 by exact_mod_cast s.ne_zero)
      have hmul : 0 < (A : ℚ) * (s : ℚ) ^ 2 := by rw [← hxval]; exact hpos
      rcases mul_pos_iff.mp hmul with h1 | h2
      · exact_mod_cast h1.1
      · exact absurd h2.2 (not_lt.mpr (le_of_lt hs2))
    have hA1 : A = 1 := by
      rcases (Int.natAbs_eq_iff.mp hAabs1) with h | h
      · exact h
      · rw [h] at hApos; omega
    refine ⟨(s : ℚ), ?_⟩
    rw [hxval, hA1]
    ring

end Work.QuadraticLocalGlobal
