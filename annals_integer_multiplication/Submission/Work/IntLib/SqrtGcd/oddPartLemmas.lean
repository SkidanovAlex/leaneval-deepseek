import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdDefs

/-!
# `oddPart`: the basic pure facts

`Work.IntLib.SG.oddPart n` is `n` with all factors of `2` removed.  This file collects the
elementary facts about it (equational lemmas, divisibility, parity, positivity, size bounds) that
the binary-gcd step `gcdStep` is analysed with.  Everything here is pure `ℕ` arithmetic.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

/-- An odd number is its own odd part. -/
theorem oddPart_eq_self_of_odd {n : ℕ} (h : n % 2 = 1) : oddPart n = n := by
  rw [oddPart.eq_def, if_neg (by rintro ⟨h1, _⟩; omega)]

/-- On a positive even number the recursion strips one factor `2`. -/
theorem oddPart_eq_half {n : ℕ} (h2 : n % 2 = 0) (hpos : 0 < n) :
    oddPart n = oddPart (n / 2) := by
  rw [oddPart.eq_def, if_pos ⟨h2, hpos⟩]

/-- The odd part divides the number. -/
theorem oddPart_dvd (n : ℕ) : oddPart n ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [oddPart.eq_def]
    by_cases h : n % 2 = 0 ∧ 0 < n
    · rw [if_pos h]
      have hlt : n / 2 < n := Nat.div_lt_self h.2 (by norm_num)
      exact Nat.dvd_trans (ih (n / 2) hlt) (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h.1))
    · rw [if_neg h]

/-- The odd part of a nonzero number is odd. -/
theorem oddPart_odd (n : ℕ) (hn : n ≠ 0) : oddPart n % 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [oddPart.eq_def]
    by_cases h : n % 2 = 0 ∧ 0 < n
    · rw [if_pos h]
      have hlt : n / 2 < n := Nat.div_lt_self h.2 (by norm_num)
      exact ih (n / 2) hlt (by omega)
    · rw [if_neg h]; omega

/-- The odd part of a nonzero number is positive. -/
theorem oddPart_pos (n : ℕ) (hn : n ≠ 0) : 0 < oddPart n := by
  have := oddPart_odd n hn; omega

/-- The odd part never exceeds the number. -/
theorem oddPart_le (n : ℕ) : oddPart n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [oddPart.eq_def]
    by_cases h : n % 2 = 0 ∧ 0 < n
    · rw [if_pos h]
      have hlt : n / 2 < n := Nat.div_lt_self h.2 (by norm_num)
      have h1 := ih (n / 2) hlt
      have h2 : n / 2 ≤ n := Nat.div_le_self n 2
      omega
    · rw [if_neg h]

/-- For a positive even number the odd part is at most half of it. -/
theorem oddPart_le_half (n : ℕ) (h2 : n % 2 = 0) (hpos : 0 < n) : oddPart n ≤ n / 2 := by
  rw [oddPart_eq_half h2 hpos]
  exact oddPart_le (n / 2)

end SG
end Work.IntLib
