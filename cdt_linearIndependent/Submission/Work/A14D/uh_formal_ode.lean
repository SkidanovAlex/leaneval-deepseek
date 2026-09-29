import Mathlib
import Submission.Work.A14D.uh_defs

/-!
# A14D — the formal ODE satisfied by `Puh = Σₙ aₙ Xⁿ`

The coefficients `aₙ = uhCoeff n` of the holomorphic solution `u_h` of `L` at `x = 1` are
defined by the three-term recurrence

`a₀ = 1`, `a₁ = 3/4`, `a_{k+2} = ((17(k+1)(k+2) + 6) a_{k+1} - 9(k+1)² a_k) / (8(k+2)²)`.

The substitution `z = 1 - w` turns the Zagier operator `LZ` into `A(w) y'' + B(w) y' + C(w) y`
with `A = Ap`, `B = Bp`, `C = Cp`.  The recurrence is precisely the coefficient form of that
differential equation, so the formal power series `Puh` satisfies

`Ap · Puh'' + Bp · Puh' + Cp · Puh = 0`.
-/

namespace Work.A14D

open PowerSeries

/-- The defining recurrence of the coefficients `uhCoeff`, in the form in which the definition
unfolds it. -/
lemma uhCoeff_rec_def (k : ℕ) :
    uhCoeff (k + 2) = ((17 * ((k : ℚ) + 1) * ((k : ℚ) + 2) + 6) * uhCoeff (k + 1)
      - 9 * ((k : ℚ) + 1) ^ 2 * uhCoeff k) / (8 * ((k : ℚ) + 2) ^ 2) := by
  rfl

/-- The operator `Ap Y'' + Bp Y' + Cp Y` expanded into monomial terms. -/
lemma uh_oper_expand :
    (Ap : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh)
    + (Bp : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Puh
    + (Cp : PowerSeries ℚ) * Puh
    = C (-8) * (X ^ 1 * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh))
      + C 17 * (X ^ 2 * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh))
      + C (-9) * (X ^ 3 * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh))
      + (C (-8) * PowerSeries.derivative (R := ℚ) Puh + C 34 * (X ^ 1 * PowerSeries.derivative (R := ℚ) Puh)
         + C (-27) * (X ^ 2 * PowerSeries.derivative (R := ℚ) Puh))
      + (C 6 * Puh + C (-9) * (X ^ 1 * Puh)) := by
  have hA : (Ap : PowerSeries ℚ) = C (-8) * X ^ 1 + C 17 * X ^ 2 + C (-9) * X ^ 3 := by
    simp only [Ap, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
      Polynomial.coe_pow]
    ring
  have hB : (Bp : PowerSeries ℚ) = C (-8) + C 34 * X ^ 1 + C (-27) * X ^ 2 := by
    simp only [Bp, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
      Polynomial.coe_pow]
    ring
  have hC : (Cp : PowerSeries ℚ) = C 6 + C (-9) * X ^ 1 := by
    simp only [Cp, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
    ring
  rw [hA, hB, hC]
  ring

theorem uh_formal_ode : (Ap : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh) + (Bp : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Puh + (Cp : PowerSeries ℚ) * Puh = 0 := by
  rw [uh_oper_expand]
  apply PowerSeries.ext
  intro n
  rw [map_zero]
  rcases n with _ | _ | _ | m
  · simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    norm_num [PowerSeries.coeff_derivative, coeff_Puh, uhCoeff]
  · simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    norm_num [PowerSeries.coeff_derivative, coeff_Puh, uhCoeff]
  · simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    norm_num [PowerSeries.coeff_derivative, coeff_Puh, uhCoeff]
  · simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      if_pos (show (1 : ℕ) ≤ m + 1 + 1 + 1 by omega),
      if_pos (show (2 : ℕ) ≤ m + 1 + 1 + 1 by omega),
      if_pos (show (3 : ℕ) ≤ m + 1 + 1 + 1 by omega),
      show (m + 1 + 1 + 1 - 1 : ℕ) = m + 2 by omega,
      show (m + 1 + 1 + 1 - 2 : ℕ) = m + 1 by omega,
      show (m + 1 + 1 + 1 - 3 : ℕ) = m by omega]
    simp only [PowerSeries.coeff_derivative, coeff_Puh]
    simp only [show (m + 1 + 1 + 1 + 1 : ℕ) = m + 2 + 2 by omega,
      show (m + 1 + 1 : ℕ) = m + 2 by omega]
    have hrec := uhCoeff_rec_def (m + 2)
    push_cast at hrec ⊢
    rw [hrec]
    field_simp
    ring

end Work.A14D
