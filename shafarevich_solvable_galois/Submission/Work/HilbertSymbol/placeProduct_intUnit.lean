/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The product formula for a pair of nonzero integers

For nonzero integers `A` and `B`, the product of the Hilbert symbols `(A,B)_v` over all places `v`
of `ℚ` equals `1` (Hilbert's product formula in the case of two rational integers).

The proof proceeds in three steps.

* The set of `x` with `placeProduct x (intUnit B) = 1` for *all* nonzero integers `B` is shown to
  be closed under the operations of interest: this is the induction lemma
  `placeProduct_intUnit_of`, whose input is that the place product with `x` is trivial against `1`,
  against `-1` and against every prime unit, and whose conclusion is the triviality against every
  nonzero integer.
* The hypotheses of that lemma are available for `x = -1` (using `placeProduct_neg_one_neg_one`
  and `placeProduct_primeUnit_neg_one`) and for `x = primeUnit q`
  (using `placeProduct_primeUnit_neg_one` and `placeProduct_primeUnit_primeUnit`).
* These two cases give the result for `x = intUnit A` by symmetry of the place product
  (`placeProduct_comm`).

The auxiliary induction `placeProduct_natCast` decomposes a positive integer into a prime `p` and
the smaller integer `n / p`, so that multiplicativity of `placeProduct` and the induction
hypothesis reduce to the prime case.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.placeProduct_mul_left
import Submission.Work.HilbertSymbol.placeProduct_mul_right
import Submission.Work.HilbertSymbol.placeProduct_comm
import Submission.Work.HilbertSymbol.placeProduct_primeUnit_primeUnit
import Submission.Work.HilbertSymbol.placeProduct_primeUnit_neg_one
import Submission.Work.HilbertSymbol.placeProduct_neg_one_neg_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.HilbertSymbol

/-- The place product with `1` in the second argument is trivial, since every local Hilbert symbol
with a `1` is trivial. -/
theorem placeProduct_one_right (x : ℚˣ) : placeProduct x 1 = 1 := by
  rw [placeProduct_def]; simp

/-- The place product with `1` in the first argument is trivial. -/
theorem placeProduct_one_left (x : ℚˣ) : placeProduct 1 x = 1 := by
  rw [placeProduct_def]; simp

/-- `intUnit` is multiplicative in the integer argument. -/
theorem intUnit_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    intUnit (a * b) (mul_ne_zero ha hb) = intUnit a ha * intUnit b hb := by
  apply Units.ext; push_cast; simp

/-- The induction step of the product formula on positive integers: a positive integer `n > 1` is
the product of a prime `p` and the smaller integer `n / p`, and `placeProduct x` is multiplicative,
so the triviality of `placeProduct x` against `p` and against `n / p` implies it against `n`. -/
theorem placeProduct_natCast (x : ℚˣ) (h1 : placeProduct x 1 = 1)
    (hpr : ∀ (q : ℕ) [Fact q.Prime], placeProduct x (primeUnit q) = 1) :
    ∀ (n : ℕ) (hn : n ≠ 0),
      placeProduct x (intUnit (n : ℤ) (by exact_mod_cast hn)) = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases eq_or_ne n 1 with h1n | hn1
    · subst h1n
      have h : intUnit ((1 : ℕ) : ℤ) (by exact_mod_cast hn) = 1 := by
        apply Units.ext; simp
      rw [h, h1]
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
      haveI : Fact p.Prime := ⟨hp⟩
      have hpne : p ≠ 0 := hp.ne_zero
      have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpdvd
      have hm : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
      have hmne : n / p ≠ 0 := (Nat.div_pos hpn hp.pos).ne'
      have hdecomp : intUnit (n : ℤ) (by exact_mod_cast hn)
          = intUnit (p : ℤ) (by exact_mod_cast hpne)
            * intUnit ((n / p : ℕ) : ℤ) (by exact_mod_cast hmne) := by
        have hn_eq : n = p * (n / p) := (Nat.mul_div_cancel' hpdvd).symm
        apply Units.ext
        simp only [Units.val_mul, intUnit_coe]
        conv_lhs => rw [hn_eq]
        push_cast
        ring
      have hpu : intUnit (p : ℤ) (by exact_mod_cast hpne) = primeUnit p := by
        apply Units.ext; simp [primeUnit, intUnit, ratUnit]
      rw [hdecomp, placeProduct_mul_right, hpu, hpr p, ih (n / p) hm hmne, one_mul]

/-- If the place product of `x` with `1`, with `-1` and with every prime unit is trivial, then it is
trivial with every nonzero integer: writing a nonzero integer `B` as `± n` with `n ≥ 0`, one uses
the positive case `placeProduct_natCast` together with multiplicativity and the case of `-1`. -/
theorem placeProduct_intUnit_of (x : ℚˣ) (h1 : placeProduct x 1 = 1)
    (hm1 : placeProduct x (-1) = 1)
    (hpr : ∀ (q : ℕ) [Fact q.Prime], placeProduct x (primeUnit q) = 1) :
    ∀ (B : ℤ) (hB : B ≠ 0), placeProduct x (intUnit B hB) = 1 := by
  intro B hB
  rcases Int.eq_nat_or_neg B with ⟨n, hn | hn⟩
  · subst hn
    have hn0 : n ≠ 0 := by
      rintro rfl; exact hB rfl
    have he : intUnit ((n : ℕ) : ℤ) hB
        = intUnit ((n : ℕ) : ℤ) (by exact_mod_cast hn0) := by
      apply Units.ext; simp
    rw [he]
    exact placeProduct_natCast x h1 hpr n hn0
  · subst hn
    have hn0 : n ≠ 0 := by
      rintro rfl; simp at hB
    have he : intUnit (-((n : ℕ) : ℤ)) hB
        = (-1 : ℚˣ) * intUnit ((n : ℕ) : ℤ) (by exact_mod_cast hn0) := by
      apply Units.ext; simp [intUnit, ratUnit]
    rw [he, placeProduct_mul_right, hm1, placeProduct_natCast x h1 hpr n hn0, one_mul]

/-- **Hilbert's product formula for a pair of nonzero integers.** The product `∏_v (A,B)_v` of the
Hilbert symbols at all places `v` of `ℚ` equals `1` for all nonzero integers `A` and `B`. -/
theorem placeProduct_intUnit (A B : ℤ) (hA : A ≠ 0) (hB : B ≠ 0) :
    placeProduct (intUnit A hA) (intUnit B hB) = 1 := by
  have hneg : ∀ (C : ℤ) (hC : C ≠ 0), placeProduct (-1) (intUnit C hC) = 1 := by
    intro C hC
    exact placeProduct_intUnit_of (-1) (placeProduct_one_right (-1))
      placeProduct_neg_one_neg_one
      (fun q _ => by rw [placeProduct_comm]; exact placeProduct_primeUnit_neg_one) C hC
  have hprime : ∀ (q : ℕ) [Fact q.Prime] (C : ℤ) (hC : C ≠ 0),
      placeProduct (primeUnit q) (intUnit C hC) = 1 := by
    intro q _ C hC
    exact placeProduct_intUnit_of (primeUnit q) (placeProduct_one_right (primeUnit q))
      placeProduct_primeUnit_neg_one
      (fun r _ => placeProduct_primeUnit_primeUnit) C hC
  refine placeProduct_intUnit_of (intUnit A hA) (placeProduct_one_right (intUnit A hA)) ?_ ?_ B hB
  · rw [placeProduct_comm]; exact hneg A hA
  · intro q _
    rw [placeProduct_comm]
    exact hprime q A hA

end Work.HilbertSymbol
