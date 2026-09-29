import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdDefs

/-!
# The odd part of a natural number: specification

`SG.oddPart n` is `n` with all factors of `2` removed.  This file proves the two facts the
binary-gcd word relies on:

* for `n ≠ 0`, `oddPart n` is odd, positive, divides `n`, and is at most `n / 2` when `n` is even;
* removing factors of `2` does not change the gcd with an odd number:
  `Nat.gcd (oddPart u) v = Nat.gcd u v` whenever `v` is odd.

The proofs are by strong induction on the argument, following the recursion of `oddPart`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open Work.IntLib

/-- Odd numbers are fixed points of `oddPart`. -/
theorem oddPart_self {n : ℕ} (h : n % 2 = 1) : SG.oddPart n = n := by
  rw [SG.oddPart.eq_def]
  simp [h]

/-- On a positive even number, `oddPart` recurses. -/
theorem oddPart_even {n : ℕ} (h2 : n % 2 = 0) (hpos : 0 < n) :
    SG.oddPart n = SG.oddPart (n / 2) := by
  rw [SG.oddPart.eq_def]
  simp [h2, hpos]

/-- `oddPart 0 = 0`. -/
theorem oddPart_zero : SG.oddPart 0 = 0 := by
  rw [SG.oddPart.eq_def]
  simp

/-- For `n ≠ 0`: `oddPart n` is odd and positive, divides `n`, and is at most `n / 2` when `n` is
even (i.e. it is the smaller of the odd candidate and — for even `n` — strictly below the input). -/
theorem oddPart_basic (n : ℕ) (hn : n ≠ 0) :
    SG.oddPart n ∣ n ∧ SG.oddPart n % 2 = 1 ∧ 0 < SG.oddPart n ∧
      (n % 2 = 0 → SG.oddPart n ≤ n / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h1
    · -- `n` even (and nonzero, so positive): recurse to `n / 2`
      have hpos : 0 < n := by omega
      have heq : SG.oddPart n = SG.oddPart (n / 2) := oddPart_even h2 hpos
      have hlt : n / 2 < n := Nat.div_lt_self hpos (by norm_num)
      have hn2 : n / 2 ≠ 0 := by omega
      obtain ⟨hdvd, hodd, hpos', -⟩ := ih (n / 2) hlt hn2
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [heq]
        exact dvd_trans hdvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h2))
      · rw [heq]; exact hodd
      · rw [heq]; exact hpos'
      · intro _
        rw [heq]
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn2) hdvd
    · -- `n` odd: `oddPart n = n`
      rw [oddPart_self h1]
      exact ⟨dvd_rfl, h1, by omega, fun h => absurd h (by omega)⟩

/-- Stripping factors of `2` from the first argument does not change the gcd with an **odd**
second argument. -/
theorem oddPart_gcd (u v : ℕ) (hv : v % 2 = 1) :
    Nat.gcd (SG.oddPart u) v = Nat.gcd u v := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    rcases eq_or_ne u 0 with rfl | hu
    · rw [oddPart_zero]
    · rcases Nat.mod_two_eq_zero_or_one u with h2 | h1
      · -- `u` even and nonzero: `u = 2 * (u / 2)`, and `2` is coprime to the odd `v`
        have hpos : 0 < u := Nat.pos_of_ne_zero hu
        have heq : SG.oddPart u = SG.oddPart (u / 2) := oddPart_even h2 hpos
        have hlt : u / 2 < u := Nat.div_lt_self hpos (by norm_num)
        rw [heq, ih (u / 2) hlt]
        conv_rhs => rw [← Nat.two_mul_div_two_of_even (Nat.even_iff.mpr h2)]
        exact (Nat.Coprime.gcd_mul_left_cancel (u / 2)
          (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hv))).symm
      · -- `u` odd
        rw [oddPart_self h1]

theorem oddPartSpec :
    (∀ n : ℕ, n ≠ 0 → (Work.IntLib.SG.oddPart n ∣ n ∧ Work.IntLib.SG.oddPart n % 2 = 1 ∧
        0 < Work.IntLib.SG.oddPart n ∧ (n % 2 = 0 → Work.IntLib.SG.oddPart n ≤ n / 2))) ∧
    (∀ u v : ℕ, v % 2 = 1 → Nat.gcd (Work.IntLib.SG.oddPart u) v = Nat.gcd u v) := by
  exact ⟨fun n hn => oddPart_basic n hn, fun u v hv => oddPart_gcd u v hv⟩

end Work.IntLib.SqrtGcd
