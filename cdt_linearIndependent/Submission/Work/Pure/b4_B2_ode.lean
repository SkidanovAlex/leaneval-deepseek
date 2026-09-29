import Mathlib
import Submission.Work.Pure.b4_defs
import Submission.Work.Pure.interfaces
import Submission.CDT.PureDenom

/-!
# The differential equation of the pure function `B₂`

`Submission.CDTPlan.B2` is the pure function

`B₂ = Σ_{n ≥ 2} 2·(n-2)!·n!/(2n)! · yⁿ`

(paper Calegari--Dimitrov--Tang, arXiv:2408.15403, eq. `(defB)`).  This module proves that it
satisfies the second displayed relation of the paper's eq. `(diffformulas)`:

`x·(4 - x)·B₂' = (2 - x)·B₂ + x²`,

coefficient by coefficient.  Writing `bₙ = [yⁿ]B₂`, the coefficient of `yⁿ` on the left is
`4n·bₙ - (n-1)·bₙ₋₁` and on the right `2·bₙ - bₙ₋₁ + [n = 2]`; both statements reduce to the pure
factorial recurrence

`(4n - 2)·bₙ - (n - 2)·bₙ₋₁ = [n = 2]`,

which is checked by hand for `n ≤ 2` and follows from `bₙ/bₙ₋₁ = (n-2)/(2(2n-1))` for `n ≥ 3`.
-/

namespace Work.Pure

open PowerSeries
open scoped BigOperators

noncomputable section

/-! ## Coefficient shifts -/

private lemma coeff_X_mul (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * f) =
      if 1 ≤ m then PowerSeries.coeff (m - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 m

private lemma coeff_Xsq (m : ℕ) :
    PowerSeries.coeff m ((PowerSeries.X : PowerSeries ℚ) ^ 2) = if m = 2 then 1 else 0 := by
  simpa using PowerSeries.coeff_X_pow m 2

private lemma coeff_C2_mul (m : ℕ) (g : PowerSeries ℚ) :
    PowerSeries.coeff m ((2 : PowerSeries ℚ) * g) = 2 * PowerSeries.coeff m g := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C_mul]

private lemma coeff_C4_mul (m : ℕ) (g : PowerSeries ℚ) :
    PowerSeries.coeff m ((4 : PowerSeries ℚ) * g) = 4 * PowerSeries.coeff m g := by
  rw [show (4 : PowerSeries ℚ) = PowerSeries.C 4 from rfl, PowerSeries.coeff_C_mul]

private lemma coeff_XD (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * PowerSeries.derivative (R := ℚ) f) =
      (m : ℚ) * PowerSeries.coeff m f := by
  rcases m with _ | k
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]; push_cast; ring

private lemma coeff_XsqD (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X ^ 2 * PowerSeries.derivative (R := ℚ) f) =
      ((m - 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) f := by
  have h : (PowerSeries.X : PowerSeries ℚ) ^ 2 * PowerSeries.derivative (R := ℚ) f
      = PowerSeries.X * (PowerSeries.X * PowerSeries.derivative (R := ℚ) f) := by ring
  rw [h]
  rcases m with _ | k
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, coeff_XD]; simp only [Nat.add_sub_cancel]

private lemma coeff_lhs (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * (4 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) f) =
      4 * ((m : ℚ) * PowerSeries.coeff m f) - ((m - 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) f := by
  rw [show PowerSeries.X * (4 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) f
      = (4 : PowerSeries ℚ) * (PowerSeries.X * PowerSeries.derivative (R := ℚ) f)
        - PowerSeries.X ^ 2 * PowerSeries.derivative (R := ℚ) f by ring]
  rw [map_sub, coeff_C4_mul, coeff_XD, coeff_XsqD]

private lemma coeff_rhs (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m ((2 - PowerSeries.X) * f + PowerSeries.X ^ 2) =
      2 * PowerSeries.coeff m f - (if 1 ≤ m then PowerSeries.coeff (m - 1) f else 0)
        + (if m = 2 then 1 else 0) := by
  rw [show (2 - PowerSeries.X) * f + PowerSeries.X ^ 2
      = (2 : PowerSeries ℚ) * f - PowerSeries.X * f + PowerSeries.X ^ 2 by ring]
  rw [map_add, map_sub, coeff_C2_mul, coeff_X_mul, coeff_Xsq]

/-! ## The coefficients of `B₂` and their recurrence -/

private lemma coeff_B2 (n : ℕ) :
    PowerSeries.coeff n Submission.CDTPlan.B2 = Submission.CDT.PureDenom.b2 n := by
  rw [Submission.CDTPlan.B2, PowerSeries.coeff_mk]
  simp only [Submission.CDT.PureDenom.b2]
  by_cases h : n < 2
  · simp [h]
  · simp only [h, if_false]
    push_cast
    ring

private lemma b2_rec (m : ℕ) :
    (4 * (m : ℚ) - 2) * Submission.CDT.PureDenom.b2 m
      - ((m : ℚ) - 2) * Submission.CDT.PureDenom.b2 (m - 1) = if m = 2 then 1 else 0 := by
  rcases lt_or_ge m 3 with h | h
  · interval_cases m <;> norm_num [Submission.CDT.PureDenom.b2]
  · have hm : ¬ m < 2 := by omega
    have hm' : ¬ m - 1 < 2 := by omega
    rw [if_neg (by omega : ¬ m = 2)]
    simp only [Submission.CDT.PureDenom.b2, if_neg hm, if_neg hm']
    rw [show (m - 1) - 2 = m - 3 by omega, show 2 * (m - 1) = 2 * m - 2 by omega]
    have h1 : (Nat.factorial m : ℚ) = (m : ℚ) * (Nat.factorial (m - 1) : ℚ) :=
      Submission.CDT.PureDenom.factorial_succ_cast m (by omega)
    have h2 : (Nat.factorial (m - 2) : ℚ) = ((m : ℚ) - 2) * (Nat.factorial (m - 3) : ℚ) := by
      have hh := Submission.CDT.PureDenom.factorial_succ_cast (m - 2) (by omega)
      rw [show m - 2 - 1 = m - 3 by omega] at hh
      rw [hh, Nat.cast_sub (by omega : 2 ≤ m)]
      push_cast; ring
    have h3 : (Nat.factorial (2 * m) : ℚ) = (2 * (m : ℚ)) * (Nat.factorial (2 * m - 1) : ℚ) :=
      Submission.CDT.PureDenom.factorial_two_mul_eq m (by omega)
    have h4 : (Nat.factorial (2 * m - 1) : ℚ)
        = (2 * (m : ℚ) - 1) * (Nat.factorial (2 * m - 2) : ℚ) := by
      have hh := Submission.CDT.PureDenom.factorial_succ_cast (2 * m - 1) (by omega)
      rw [show 2 * m - 1 - 1 = 2 * m - 2 by omega] at hh
      rw [hh, Nat.cast_sub (by omega : 1 ≤ 2 * m)]
      push_cast; ring
    rw [h1, h2, h3, h4]
    have e1 : (Nat.factorial (m - 3) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m - 3)
    have e2 : (Nat.factorial (m - 1) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m - 1)
    have e3 : (Nat.factorial (2 * m - 2) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * m - 2)
    have e4 : (m : ℚ) ≠ 0 := by positivity
    have e5 : (2 * (m : ℚ)) ≠ 0 := by positivity
    have e6 : (2 * (m : ℚ) - 1) ≠ 0 := by
      have : (1 : ℚ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      linarith
    have e7 : ((m : ℚ) * 2 - 1) ≠ 0 := by
      have : (1 : ℚ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      linarith
    field_simp
    ring

/-! ## The differential equation -/

theorem b4_B2_ode : PowerSeries.X * (4 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B2 = (2 - PowerSeries.X) * Submission.CDTPlan.B2 + PowerSeries.X ^ 2 := by
  apply PowerSeries.ext
  intro m
  rw [coeff_lhs m Submission.CDTPlan.B2, coeff_rhs m Submission.CDTPlan.B2, coeff_B2, coeff_B2]
  rcases lt_or_ge m 3 with hm | hm
  · interval_cases m <;> norm_num [Submission.CDT.PureDenom.b2]
  · have h1 : 1 ≤ m := by omega
    have h2 : ¬ m = 2 := by omega
    rw [if_pos h1, if_neg h2]
    have hc : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by rw [Nat.cast_sub h1]; ring
    rw [hc]
    have hb := b2_rec m
    rw [if_neg h2] at hb
    linear_combination hb

end

end Work.Pure
