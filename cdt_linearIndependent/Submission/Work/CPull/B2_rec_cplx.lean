import Mathlib
import Submission.Work.Pure.b4_B2_ode

/-!
# The coefficient recurrence of `B₂` over `ℂ`

`Submission.CDTPlan.B2` is the pure function `B₂ = Σ_{n ≥ 2} 2·(n-2)!·n!/(2n)! · yⁿ`
(paper Calegari--Dimitrov--Tang, arXiv:2408.15403, eq. `(defB)`), and `Work.Pure.b4_B2_ode`
proves the formal identity `X·(4 - X)·B₂' = (2 - X)·B₂ + X²`.

This module extracts the coefficient form of that identity, in which the coefficients
`cₙ = [yⁿ]B₂` (rational numbers, cast to `ℂ`) satisfy

`4·n·cₙ - (n-1)·cₙ₋₁ = 2·cₙ - cₙ₋₁ + [n = 2]`,

with the convention `c₋₁ = c₀` (i.e. the term `cₙ₋₁` is dropped for `n = 0`).
This is exactly the recurrence fed to `Work.CPull.evp_ode_of_rec` in `evp_B2_ode`.
-/

namespace Work.CPull

open PowerSeries

noncomputable section

/-! ## Coefficient of the two sides of `X·(4 - X)·B₂' = (2 - X)·B₂ + X²` -/

private lemma coeff_X_mul (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * f) =
      if 1 ≤ m then PowerSeries.coeff (m - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 m

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

private lemma coeff_C2_mul (m : ℕ) (g : PowerSeries ℚ) :
    PowerSeries.coeff m ((2 : PowerSeries ℚ) * g) = 2 * PowerSeries.coeff m g := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C_mul]

private lemma coeff_C4_mul (m : ℕ) (g : PowerSeries ℚ) :
    PowerSeries.coeff m ((4 : PowerSeries ℚ) * g) = 4 * PowerSeries.coeff m g := by
  rw [show (4 : PowerSeries ℚ) = PowerSeries.C 4 from rfl, PowerSeries.coeff_C_mul]

private lemma coeff_Xsq (m : ℕ) :
    PowerSeries.coeff m ((PowerSeries.X : PowerSeries ℚ) ^ 2) = if m = 2 then 1 else 0 := by
  simpa using PowerSeries.coeff_X_pow m 2

private lemma coeff_lhs (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * (4 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) f) =
      4 * ((m : ℚ) * PowerSeries.coeff m f)
        - ((m - 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) f := by
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

/-! ## The recurrence over `ℚ`, then over `ℂ` -/

/-- Coefficient form of `Work.Pure.b4_B2_ode` over `ℚ`. -/
private theorem B2_rec_rat (m : ℕ) :
    4 * ((m : ℚ) * PowerSeries.coeff m Submission.CDTPlan.B2)
      - (((m - 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) Submission.CDTPlan.B2)
    = 2 * PowerSeries.coeff m Submission.CDTPlan.B2
      - (if m = 0 then 0 else PowerSeries.coeff (m - 1) Submission.CDTPlan.B2)
      + (if m = 2 then 1 else 0) := by
  have h := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff m f) Work.Pure.b4_B2_ode
  rw [coeff_lhs, coeff_rhs] at h
  rw [h]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm, if_pos (by omega : 1 ≤ m)]

/-- The coefficient recurrence of `B₂`, with all coefficients regarded as complex numbers. -/
theorem B2_rec_cplx (n : ℕ) :
    4 * ((n : ℂ) * ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ))
      - (((n - 1 : ℕ) : ℂ) * ((PowerSeries.coeff (n - 1) Submission.CDTPlan.B2 : ℚ) : ℂ))
    = 2 * ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)
      - (if n = 0 then 0 else ((PowerSeries.coeff (n - 1) Submission.CDTPlan.B2 : ℚ) : ℂ))
      + (if n = 2 then 1 else 0) := by
  have h' := congrArg (fun z : ℚ => (z : ℂ)) (B2_rec_rat n)
  push_cast at h'
  rw [show (((if n = 0 then (0 : ℚ)
        else PowerSeries.coeff (n - 1) Submission.CDTPlan.B2 : ℚ)) : ℂ)
      = (if n = 0 then 0
          else ((PowerSeries.coeff (n - 1) Submission.CDTPlan.B2 : ℚ) : ℂ)) from by
        split_ifs <;> norm_num] at h'
  rw [show (((if n = 2 then (1 : ℚ) else 0 : ℚ)) : ℂ) = (if n = 2 then (1 : ℂ) else 0) from by
        split_ifs <;> norm_num] at h'
  exact h'

end

end Work.CPull
