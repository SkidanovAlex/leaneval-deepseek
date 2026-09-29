import Mathlib
import Submission.Work.Pure.interfaces

namespace Work.Pure

open Submission.CDTPlan
open PowerSeries

/-!
# `b5_rel`: the differential equation satisfied by the pure function `B₅`

We prove, coefficient by coefficient, the identity

`2 * X * (4 - X) * (d/dX) B₅ = (4 - X) * B₅ - 2 * B₂ + 4 * X`

(the paper's equation relating `B₅` to `B₂`).

The coefficient of `Xⁿ` on the left is `8 n [Xⁿ]B₅ - 2 (n-1) [Xⁿ⁻¹]B₅`, and on the right
`4 [Xⁿ]B₅ - [Xⁿ⁻¹]B₅ - 2 [Xⁿ]B₂ + 4·[n=1]`.  For `n ≥ 2` these agree because of the
coefficient recurrence

`(8n-4) [Xⁿ]B₅ - (2n-3) [Xⁿ⁻¹]B₅ + 2 [Xⁿ]B₂ = 0,

which is a pure factorial identity, and for `n = 0, 1` the two sides are checked directly.
-/

/-! ## Coefficient shifts -/

lemma b5_coeff_X_mul_deriv (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (X * (PowerSeries.derivative (R := ℚ)) f) = (n : ℚ) * PowerSeries.coeff n f := by
  rcases n with _ | m
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]; push_cast; ring

lemma b5_coeff_Xsq_mul_deriv (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (X ^ 2 * (PowerSeries.derivative (R := ℚ)) f) =
      ((n - 1 : ℕ) : ℚ) * PowerSeries.coeff (n - 1) f := by
  have h : (X : PowerSeries ℚ) ^ 2 * (PowerSeries.derivative (R := ℚ)) f
        = X * (X * (PowerSeries.derivative (R := ℚ)) f) := by ring
  rw [h]
  rcases n with _ | m
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, b5_coeff_X_mul_deriv]
    simp only [Nat.add_sub_cancel]

/-- Coefficient of the left-hand side `2 X (4 - X) d/dX` of `b5_rel`. -/
lemma b5_coeff_lhs (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (2 * (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) f)
      = 2 * (4 * (n : ℚ) * PowerSeries.coeff n f
             - ((n - 1 : ℕ) : ℚ) * PowerSeries.coeff (n - 1) f) := by
  have h : 2 * (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) f
        = 8 * (X * (PowerSeries.derivative (R := ℚ)) f)
            - 2 * (X ^ 2 * (PowerSeries.derivative (R := ℚ)) f) := by ring
  rw [h]
  have h8 : (8 : PowerSeries ℚ) = PowerSeries.C 8 := rfl
  have h2 : (2 : PowerSeries ℚ) = PowerSeries.C 2 := rfl
  rw [h8, h2, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      b5_coeff_X_mul_deriv, b5_coeff_Xsq_mul_deriv]
  ring

/-! ## Base coefficients -/

lemma b5_coeff_B5_zero : PowerSeries.coeff 0 B5 = 0 := by simp [B5]
lemma b5_coeff_B5_one : PowerSeries.coeff 1 B5 = 1 := by norm_num [B5]
lemma b5_coeff_B2_zero : PowerSeries.coeff 0 B2 = 0 := by simp [B2]
lemma b5_coeff_B2_one : PowerSeries.coeff 1 B2 = 0 := by norm_num [B2]

lemma b5_coeff_X_mul_B5 (n : ℕ) :
    PowerSeries.coeff n (X * B5) = PowerSeries.coeff (n - 1) B5 := by
  rcases n with _ | m
  · rw [PowerSeries.coeff_zero_X_mul, b5_coeff_B5_zero]
  · rw [PowerSeries.coeff_succ_X_mul, Nat.add_sub_cancel]

/-- Coefficient of the right-hand side `(4 - X) B₅ - 2 B₂ + 4 X` of `b5_rel`. -/
lemma b5_coeff_rhs (n : ℕ) :
    PowerSeries.coeff n ((4 - X) * B5 - 2 * B2 + 4 * X)
      = 4 * PowerSeries.coeff n B5 - PowerSeries.coeff (n - 1) B5 - 2 * PowerSeries.coeff n B2
        + 4 * (if n = 1 then 1 else 0) := by
  have h4 : (4 : PowerSeries ℚ) = PowerSeries.C 4 := rfl
  have h2 : (2 : PowerSeries ℚ) = PowerSeries.C 2 := rfl
  rw [h4, h2]
  rw [sub_mul, map_add, map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_C_mul, b5_coeff_X_mul_B5, PowerSeries.coeff_X]

/-! ## The factorial recurrence -/

private lemma b5_recur_j (j : ℕ) :
    (8 * (↑(j + 2) : ℚ) - 4) * PowerSeries.coeff (j + 2) B5
      - (2 * (↑(j + 2) : ℚ) - 3) * PowerSeries.coeff (j + 1) B5
      + 2 * PowerSeries.coeff (j + 2) B2 = 0 := by
  have h5a : PowerSeries.coeff (j + 2) B5
      = ((j + 1).factorial : ℚ) ^ 2 / (((2 * j + 3).factorial : ℚ) * (2 * (j : ℚ) + 3)) := by
    simp only [B5, PowerSeries.coeff_mk, if_neg (show ¬ (j + 2 = 0) by omega)]
    have e1 : j + 2 - 1 = j + 1 := by omega
    have e2 : 2 * (j + 2) - 1 = 2 * j + 3 := by omega
    rw [e1, e2]; push_cast; ring
  have h5b : PowerSeries.coeff (j + 1) B5
      = ((j).factorial : ℚ) ^ 2 / (((2 * j + 1).factorial : ℚ) * (2 * (j : ℚ) + 1)) := by
    simp only [B5, PowerSeries.coeff_mk, if_neg (show ¬ (j + 1 = 0) by omega)]
    have e1 : j + 1 - 1 = j := by omega
    have e2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [e1, e2]; push_cast; ring
  have h2a : PowerSeries.coeff (j + 2) B2
      = 2 * ((j.factorial * (j + 2).factorial : ℕ) : ℚ) / ((2 * j + 4).factorial : ℚ) := by
    simp only [B2, PowerSeries.coeff_mk, if_neg (show ¬ (j + 2 < 2) by omega)]
    have e1 : j + 2 - 2 = j := by omega
    have e2 : 2 * (j + 2) = 2 * j + 4 := by omega
    rw [e1, e2]; push_cast; ring
  rw [h5a, h5b, h2a]
  push_cast
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Coefficient recurrence `(8n-4)[Xⁿ]B₅ - (2n-3)[Xⁿ⁻¹]B₅ + 2[Xⁿ]B₂ = 0` for `n ≥ 2`. -/
private lemma b5_recur (k : ℕ) (hk : 2 ≤ k) :
    (8 * (k : ℚ) - 4) * PowerSeries.coeff k B5
      - (2 * (k : ℚ) - 3) * PowerSeries.coeff (k - 1) B5
      + 2 * PowerSeries.coeff k B2 = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  subst hj
  rw [show j + 2 - 1 = j + 1 from by omega]
  exact b5_recur_j j

/-! ## The main identity -/

theorem b5_rel :
    2 * (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) B5
      = (4 - X) * B5 - 2 * B2 + 4 * X := by
  ext n
  rw [b5_coeff_lhs B5 n, b5_coeff_rhs n]
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;>
      norm_num [b5_coeff_B5_zero, b5_coeff_B5_one, b5_coeff_B2_zero, b5_coeff_B2_one]
  · have hne : n ≠ 1 := by omega
    rw [if_neg hne]
    have hcast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    rw [hcast]
    have hr := b5_recur n hn
    linear_combination hr

end Work.Pure
