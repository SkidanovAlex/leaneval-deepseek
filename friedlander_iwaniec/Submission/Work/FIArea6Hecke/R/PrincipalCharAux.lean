/-
# `Submission.Work.FIArea6Hecke.R.PrincipalCharAux`

Elementary vocabulary for the principal-character logarithmic-derivative bound
`Work.FIArea6Hecke.R.heckeLSeries_logDeriv_principalChar`.

The principal (trivial) strict character modulo `4d` is `chiTriv d` (`1` on the units of
`ℤ[i]/(4d)`, `0` off them).  Its Hecke `L`-series of weight `0` factorises, on `re s > 1`, as

  `L(s) = ζ(s) · L(s, χ₄) · G_d(s)`,

where `χ₄` is the quadratic character modulo `4` (the character of `ℚ(i)/ℚ`) and

  `G_d(s) = ∏_{p ∣ 4d} (1 - p^{-s})(1 - χ₄(p)p^{-s})`

is the finite product removing the Euler factors at the primes dividing `4d`.  This file fixes the
two objects `chi4fun` (the character on `ℕ`) and `badPoly` (`G_d`) and their elementary, proved API;
the arithmetic and analytic facts about them are delegated.
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- The quadratic character `χ₄` modulo `4`, as a function on `ℕ`. -/
def chi4fun (n : ℕ) : ℂ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℂ)

@[simp] lemma chi4fun_zero : chi4fun 0 = 0 := by simp [chi4fun]

@[simp] lemma chi4fun_one : chi4fun 1 = 1 := by simp [chi4fun]

/-- Explicit values: `χ₄ n = 0` for even `n`, `1` for `n ≡ 1 (4)`, `-1` for `n ≡ 3 (4)`. -/
lemma chi4fun_eq_if (n : ℕ) :
    chi4fun n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  rw [chi4fun, ZMod.χ₄_nat_eq_if_mod_four]
  push_cast
  by_cases h : n % 2 = 0 <;> simp [h]

lemma chi4fun_norm_le_one (n : ℕ) : ‖chi4fun n‖ ≤ 1 := by
  rw [chi4fun_eq_if]; split_ifs <;> norm_num

lemma chi4fun_mul (m n : ℕ) : chi4fun (m * n) = chi4fun m * chi4fun n := by
  simp only [chi4fun, Nat.cast_mul]
  rw [map_mul]
  push_cast
  ring

lemma chi4fun_eq_neg_one_of_mod_four {n : ℕ} (h : n % 4 = 3) : chi4fun n = -1 := by
  rw [chi4fun_eq_if, if_neg (by omega), if_neg (by omega)]

lemma chi4fun_eq_one_of_mod_four {n : ℕ} (h : n % 4 = 1) : chi4fun n = 1 := by
  rw [chi4fun_eq_if, if_neg (by omega), if_pos h]

lemma chi4fun_eq_zero_of_even {n : ℕ} (h : n % 2 = 0) : chi4fun n = 0 := by
  rw [chi4fun_eq_if, if_pos h]

/-- The value of `χ₄` at a prime. -/
lemma chi4fun_prime {p : ℕ} (hp : p.Prime) :
    chi4fun p = if p = 2 then 0 else if p % 4 = 1 then 1 else -1 := by
  rw [chi4fun_eq_if]
  rcases hp.eq_two_or_odd' with h | h
  · subst h; simp
  · have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd h (by decide)
    have hodd : p % 2 = 1 := Nat.odd_iff.mp h
    rw [if_neg (by omega : ¬ p % 2 = 0), if_neg hp2]

/-- The finite Euler-factor correction `G_d(s) = ∏_{p ∣ 4d}(1-p^{-s})(1-χ₄(p)p^{-s})`. -/
def badPoly (d : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ (4 * d).primeFactors, (1 - (p : ℂ) ^ (-s)) * (1 - chi4fun p * (p : ℂ) ^ (-s))

lemma badPoly_congr {d d' : ℕ} (h : d = d') (s : ℂ) : badPoly d s = badPoly d' s := by
  subst h; rfl

end

end Work.FIArea6Hecke.R
