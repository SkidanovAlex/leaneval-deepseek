import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.CDT.PureDenom
import Submission.Work.Pure.b4_denom
import Submission.Work.Pure.b4_rel
import Submission.Work.Pure.b5_rel

/-!
# Area Pure — the seven pure functions `B₁,…,B₇` (`Submission.CDTPlan.PureFacts`)

Paper: Calegari–Dimitrov–Tang, arXiv:2408.15403, §"Pure functions"
(eqs. `(defB)`, `(defB5)`, `(defB67)` and Lemma `bdenominators`).

This module proves `Submission.CDTPlan.PureFacts`, i.e. the denominator types
of `B₁,…,B₇` and the `D`-closure of their `ℚ(y)`-span.

* Denominator types of `B₁,B₂,B₃,B₅` come from the explicit factorial/binomial
  coefficients (`Submission.CDT.PureDenom`).
* The denominator type of `B₄` (`Sym⁻Li₂`, the double-binomial series) and the
  first-order relations for `B₄`, `B₅` are supplied by the sibling modules
  `Submission.Work.Pure.b4_denom`, `b4_rel`, `b5_rel`.
* `B₇` inherits its denominator type from `B₄` (`B₇ = ∫B₄/y`).
* The `D`-closure uses the paper's eq. `(diffformulas)`.
-/

namespace Work.Pure

open Submission.CDTPlan
open PowerSeries
open scoped BigOperators

private noncomputable abbrev pb2 (n : ℕ) : ℚ := Submission.CDT.PureDenom.b2 n
private noncomputable abbrev pb3 (n : ℕ) : ℚ := Submission.CDT.PureDenom.b3 n
private noncomputable abbrev pb5 (n : ℕ) : ℚ := Submission.CDT.PureDenom.b5 n
private noncomputable abbrev pb6 (n : ℕ) : ℚ := Submission.CDT.PureDenom.b6 n

/-! ## Divisibility of `lcmUpto` -/

lemma dvd_lcmUpto {k N : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ N) : k ∣ lcmUpto N := by
  unfold lcmUpto
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨h1, h2⟩)

lemma lcmUpto_zero : lcmUpto 0 = 1 := by simp [lcmUpto]

/-! ## Coefficients of the pure functions -/

lemma coeff_B1 (n : ℕ) : PowerSeries.coeff n B1 = if n = 0 then 1 else 0 :=
  PowerSeries.coeff_one n

lemma coeff_B2 (n : ℕ) : PowerSeries.coeff n B2 = pb2 n := by
  rw [B2, PowerSeries.coeff_mk]
  simp only [pb2, Submission.CDT.PureDenom.b2]
  by_cases h : n < 2
  · simp [h]
  · simp only [h, if_false]
    push_cast
    ring

lemma coeff_B3 (n : ℕ) : PowerSeries.coeff n B3 = pb3 n := by
  rw [B3, PowerSeries.coeff_mk]
  simp only [pb3, Submission.CDT.PureDenom.b3]

lemma coeff_B5 (n : ℕ) : PowerSeries.coeff n B5 = pb5 n := by
  rw [B5, PowerSeries.coeff_mk]
  simp only [pb5, Submission.CDT.PureDenom.b5]
  by_cases h : n = 0
  · simp [h]
  · simp only [h, if_false]
    rw [show (((2 * n - 1 : ℕ)) : ℚ) = 2 * (n : ℚ) - 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring]

lemma coeff_B6 (n : ℕ) : PowerSeries.coeff n B6 = pb6 n := by
  rw [B6, PowerSeries.coeff_mk]
  simp only [pb6, Submission.CDT.PureDenom.b6]

lemma coeff_B7 (n : ℕ) :
    PowerSeries.coeff n B7 = if n = 0 then 0 else PowerSeries.coeff n B4 / (n : ℚ) := by
  rw [B7, PowerSeries.coeff_mk]

/-! ## Coefficient recurrences -/

lemma coeff_X_mul (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (X * f) = if 1 ≤ m then PowerSeries.coeff (m - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 m

lemma coeff_X_sq_mul (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (X ^ 2 * f) = if 2 ≤ m then PowerSeries.coeff (m - 2) f else 0 :=
  PowerSeries.coeff_X_pow_mul' f 2 m

lemma coeff_X_sq (m : ℕ) :
    PowerSeries.coeff m (X ^ 2 : PowerSeries ℚ) = if m = 2 then 1 else 0 :=
  PowerSeries.coeff_X_pow m 2

lemma coeff_deriv (k : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff k ((PowerSeries.derivative (R := ℚ)) f) =
      ((k : ℚ) + 1) * PowerSeries.coeff (k + 1) f := by
  rw [PowerSeries.coeff_derivative]; push_cast; ring

lemma b2_rec (m : ℕ) :
    (4 * (m : ℚ) - 2) * pb2 m - ((m : ℚ) - 2) * pb2 (m - 1) = if m = 2 then 1 else 0 := by
  rcases lt_or_ge m 3 with h | h
  · interval_cases m <;> norm_num [pb2, Submission.CDT.PureDenom.b2]
  · have hm : ¬ m < 2 := by omega
    have hm' : ¬ m - 1 < 2 := by omega
    rw [if_neg (by omega : ¬ m = 2)]
    simp only [pb2, Submission.CDT.PureDenom.b2, if_neg hm, if_neg hm']
    rw [show (m-1)-2 = m-3 by omega, show 2*(m-1) = 2*m-2 by omega]
    have h1 : (Nat.factorial m : ℚ) = (m:ℚ) * (Nat.factorial (m-1) : ℚ) :=
      Submission.CDT.PureDenom.factorial_succ_cast m (by omega)
    have h2 : (Nat.factorial (m-2) : ℚ) = ((m:ℚ)-2) * (Nat.factorial (m-3) : ℚ) := by
      have hh := Submission.CDT.PureDenom.factorial_succ_cast (m-2) (by omega)
      rw [show m-2-1 = m-3 by omega] at hh
      rw [hh, Nat.cast_sub (by omega : 2 ≤ m)]
      push_cast; ring
    have h3 : (Nat.factorial (2*m) : ℚ) = (2*(m:ℚ)) * (Nat.factorial (2*m-1) : ℚ) :=
      Submission.CDT.PureDenom.factorial_two_mul_eq m (by omega)
    have h4 : (Nat.factorial (2*m-1) : ℚ) = (2*(m:ℚ)-1) * (Nat.factorial (2*m-2) : ℚ) := by
      have hh := Submission.CDT.PureDenom.factorial_succ_cast (2*m-1) (by omega)
      rw [show 2*m-1-1 = 2*m-2 by omega] at hh
      rw [hh, Nat.cast_sub (by omega : 1 ≤ 2*m)]
      push_cast; ring
    rw [h1, h2, h3, h4]
    have e1 : (Nat.factorial (m-3) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m-3)
    have e2 : (Nat.factorial (m-1) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m-1)
    have e3 : (Nat.factorial (2*m-2) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*m-2)
    have e4 : (m:ℚ) ≠ 0 := by positivity
    have e5 : (2*(m:ℚ)) ≠ 0 := by positivity
    have e6 : (2*(m:ℚ)-1) ≠ 0 := by
      have : (1:ℚ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      linarith
    have e7 : ((m:ℚ)*2 - 1) ≠ 0 := by
      have : (1:ℚ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      linarith
    field_simp
    ring

lemma b3_rec (m : ℕ) :
    4 * (m : ℚ) * pb3 m - ((m : ℚ) - 1) * pb3 (m - 1) + pb2 m = if m = 1 then 2 else 0 := by
  rcases lt_or_ge m 3 with h | h
  · interval_cases m <;>
      norm_num [pb3, pb2, Submission.CDT.PureDenom.b3, Submission.CDT.PureDenom.b2]
  · have hm : ¬ m < 2 := by omega
    have hm1 : ¬ m - 1 = 0 := by omega
    have hm0 : ¬ m = 0 := by omega
    simp only [pb3, pb2, Submission.CDT.PureDenom.b3, Submission.CDT.PureDenom.b2, if_neg hm0,
      if_neg hm, if_neg hm1, if_neg (by omega : ¬ m = 1)]
    rw [show m-1-1 = m-2 by omega, show 2*(m-1) = 2*m-2 by omega]
    have h1 : (Nat.factorial m : ℚ) = (m:ℚ) * (Nat.factorial (m-1) : ℚ) :=
      Submission.CDT.PureDenom.factorial_succ_cast m (by omega)
    have h2 : (Nat.factorial (m-2) : ℚ) = ((m:ℚ)-2) * (Nat.factorial (m-3) : ℚ) := by
      have hh := Submission.CDT.PureDenom.factorial_succ_cast (m-2) (by omega)
      rw [show m-2-1 = m-3 by omega] at hh
      rw [hh, Nat.cast_sub (by omega : 2 ≤ m)]
      push_cast; ring
    have h3 : (Nat.factorial (2*m) : ℚ) = (2*(m:ℚ)) * (Nat.factorial (2*m-1) : ℚ) :=
      Submission.CDT.PureDenom.factorial_two_mul_eq m (by omega)
    have h4 : (Nat.factorial (2*m-1) : ℚ) = (2*(m:ℚ)-1) * (Nat.factorial (2*m-2) : ℚ) := by
      have hh := Submission.CDT.PureDenom.factorial_succ_cast (2*m-1) (by omega)
      rw [show 2*m-1-1 = 2*m-2 by omega] at hh
      rw [hh, Nat.cast_sub (by omega : 1 ≤ 2*m)]
      push_cast; ring
    have h1' : (Nat.factorial (m-1) : ℚ) = ((m:ℚ)-1) * (Nat.factorial (m-2) : ℚ) := by
      have hh := Submission.CDT.PureDenom.factorial_succ_cast (m-1) (by omega)
      rw [show m-1-1 = m-2 by omega] at hh
      rw [hh, Nat.cast_sub (by omega : 1 ≤ m)]
      push_cast; ring
    rw [h1, h1', h2, h3, h4]
    have e1 : (Nat.factorial (m-3) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m-3)
    have e2 : (Nat.factorial (m-1) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m-1)
    have e3 : (Nat.factorial (2*m-2) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*m-2)
    have e4 : (m:ℚ) ≠ 0 := by positivity
    have e5 : (2*(m:ℚ)) ≠ 0 := by positivity
    have e6 : (2*(m:ℚ)-1) ≠ 0 := by
      have : (1:ℚ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      linarith
    have e7 : ((m:ℚ)*2 - 1) ≠ 0 := by
      have : (1:ℚ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      linarith
    field_simp
    ring

lemma b6_mul (m : ℕ) : (m : ℚ) * pb6 m = pb3 m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; norm_num [pb6, pb3, Submission.CDT.PureDenom.b6, Submission.CDT.PureDenom.b3]
  · simp only [pb6, pb3, Submission.CDT.PureDenom.b6, Submission.CDT.PureDenom.b3,
      if_neg (by omega : ¬ m = 0)]
    have hm : (m : ℚ) ≠ 0 := by positivity
    have hf : (Nat.factorial (m-1) : ℚ) ^ 2 ≠ 0 := by
      have := Nat.factorial_ne_zero (m-1)
      positivity
    have hg : (Nat.factorial (2*m) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*m)
    field_simp

lemma b7_mul (m : ℕ) : (m : ℚ) * PowerSeries.coeff m B7 = PowerSeries.coeff m B4 := by
  rw [coeff_B7]
  by_cases h : m = 0
  · subst h
    rw [B4, PowerSeries.coeff_mk]; simp
  · rw [if_neg h]
    have hm : (m : ℚ) ≠ 0 := by positivity
    exact mul_div_cancel₀ _ hm

/-! ## The first-order differential relations (paper eq. `(diffformulas)`) -/

lemma B2_rel_aux :
    PowerSeries.C 2 * (X : PowerSeries ℚ) * (PowerSeries.C 4 - X) * (PowerSeries.derivative (R := ℚ)) B2
      = PowerSeries.C 2 * X ^ 2 + (PowerSeries.C 4 - PowerSeries.C 2 * X) * B2 := by
  apply PowerSeries.ext
  intro m
  rw [show PowerSeries.C 2 * (X : PowerSeries ℚ) * (PowerSeries.C 4 - X) * (PowerSeries.derivative (R := ℚ)) B2
        = PowerSeries.C 2 * (PowerSeries.C 4 * (X * (PowerSeries.derivative (R := ℚ)) B2)
            - X ^ 2 * (PowerSeries.derivative (R := ℚ)) B2) by ring]
  rw [show PowerSeries.C 2 * X ^ 2 + (PowerSeries.C 4 - PowerSeries.C 2 * X) * B2
        = PowerSeries.C 2 * X ^ 2 + (PowerSeries.C 4 * B2 - PowerSeries.C 2 * (X * B2)) by ring]
  rcases lt_or_ge m 4 with hm | hm
  · interval_cases m <;>
      (simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_mul, coeff_X_sq_mul,
        coeff_X_sq, PowerSeries.coeff_X, coeff_deriv, coeff_B2, pb2,
        Submission.CDT.PureDenom.b2] <;> norm_num)
  · have e1 : 1 ≤ m := by omega
    have e2 : 2 ≤ m := by omega
    have e3 : ¬ m = 2 := by omega
    have h1 : m - 1 + 1 = m := by omega
    have h2 : m - 2 + 1 = m - 1 := by omega
    have hc1 : ((m - 1 : ℕ) : ℚ) + 1 = (m : ℚ) := by rw [Nat.cast_sub e1]; ring
    have hc2 : ((m - 2 : ℕ) : ℚ) + 1 = (m : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 2 ≤ m)]; ring
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_mul, coeff_X_sq_mul, coeff_X_sq,
      coeff_deriv, if_pos e1, if_pos e2, if_neg e3]
    simp only [coeff_B2, h1, h2, hc1, hc2]
    have hb := b2_rec m
    rw [if_neg e3] at hb
    linear_combination 2 * hb

lemma B3_rel_aux :
    PowerSeries.C 2 * (X : PowerSeries ℚ) * (PowerSeries.C 4 - X) * (PowerSeries.derivative (R := ℚ)) B3
      = PowerSeries.C 4 * X - PowerSeries.C 2 * B2 := by
  apply PowerSeries.ext
  intro m
  rw [show PowerSeries.C 2 * (X : PowerSeries ℚ) * (PowerSeries.C 4 - X) * (PowerSeries.derivative (R := ℚ)) B3
        = PowerSeries.C 2 * (PowerSeries.C 4 * (X * (PowerSeries.derivative (R := ℚ)) B3)
            - X ^ 2 * (PowerSeries.derivative (R := ℚ)) B3) by ring]
  rcases lt_or_ge m 4 with hm | hm
  · interval_cases m <;>
      (simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_mul, coeff_X_sq_mul,
        coeff_X_sq, PowerSeries.coeff_X, coeff_deriv, coeff_B2, coeff_B3, pb2, pb3,
        Submission.CDT.PureDenom.b2, Submission.CDT.PureDenom.b3] <;> norm_num)
  · have e1 : 1 ≤ m := by omega
    have e2 : 2 ≤ m := by omega
    have e3 : ¬ m = 1 := by omega
    have h1 : m - 1 + 1 = m := by omega
    have h2 : m - 2 + 1 = m - 1 := by omega
    have hc1 : ((m - 1 : ℕ) : ℚ) + 1 = (m : ℚ) := by rw [Nat.cast_sub e1]; ring
    have hc2 : ((m - 2 : ℕ) : ℚ) + 1 = (m : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 2 ≤ m)]; ring
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_mul, coeff_X_sq_mul, coeff_X_sq,
      PowerSeries.coeff_X, coeff_deriv, if_pos e1, if_pos e2, if_neg e3]
    simp only [coeff_B2, coeff_B3, h1, h2, hc1, hc2]
    have hb := b3_rec m
    rw [if_neg e3] at hb
    linear_combination 2 * hb

lemma relation_B2 :
    2 * (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) B2
      = 2 * X ^ 2 + (4 - 2 * X) * B2 :=
  B2_rel_aux

lemma relation_B3 :
    2 * (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) B3
      = 4 * X - 2 * B2 :=
  B3_rel_aux

lemma relation_B6 :
    2 * (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) B6
      = 2 * (4 - X) * B3 := by
  have h : (X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B6 = B3 := by
    apply PowerSeries.ext
    intro m
    rw [coeff_X_mul, coeff_B3]
    by_cases hm : 1 ≤ m
    · rw [if_pos hm, coeff_deriv, show m - 1 + 1 = m by omega]
      have hc : ((m - 1 : ℕ) : ℚ) + 1 = (m : ℚ) := by rw [Nat.cast_sub hm]; ring
      rw [hc, coeff_B6]
      exact b6_mul m
    · rw [if_neg hm]
      have hm0 : m = 0 := by omega
      subst hm0
      simp [pb3, Submission.CDT.PureDenom.b3]
  rw [← h]
  ring

lemma relation_B7 :
    2 * (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) B7
      = 2 * (4 - X) * B4 := by
  have h : (X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B7 = B4 := by
    apply PowerSeries.ext
    intro m
    rw [coeff_X_mul]
    by_cases hm : 1 ≤ m
    · rw [if_pos hm, coeff_deriv, show m - 1 + 1 = m by omega]
      have hc : ((m - 1 : ℕ) : ℚ) + 1 = (m : ℚ) := by rw [Nat.cast_sub hm]; ring
      rw [hc]
      exact b7_mul m
    · rw [if_neg hm]
      have hm0 : m = 0 := by omega
      subst hm0
      have h := b7_mul 0
      simp only [Nat.cast_zero, zero_mul] at h
      exact h
  rw [← h]
  ring

lemma relation_B4 :
    2 * (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) B4
      = 2 * (2 - X) * B4 + 2 * (4 - X) * B2 - 4 * X * (4 - X) := by
  have h := congrArg (fun z : PowerSeries ℚ => (2 : PowerSeries ℚ) * z) b4_rel
  rw [show (2 : PowerSeries ℚ) * ((X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) B4)
        = 2 * (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) B4 by ring] at h
  rw [h]
  ring

lemma relation_B5 :
    2 * (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) B5
      = (4 - X) * B5 - 2 * B2 + 4 * X :=
  b5_rel

/-! ## Denominator types -/

theorem b1_denom : HasDenomType 0 ![0, 0] B1 := by
  refine ⟨1, 0, by norm_num, fun n hn => ⟨0, ?_⟩⟩
  have hc : PowerSeries.coeff n B1 = 0 := by
    rw [coeff_B1, if_neg (by omega : ¬ n = 0)]
  rw [hc]; simp

theorem b2_denom : HasDenomType 0 ![2, 0] B2 := by
  refine ⟨1, 0, by norm_num, fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := Submission.CDT.PureDenom.int_lcmUpto_mul_b2 n
  refine ⟨z, ?_⟩
  have hprod : (∏ j : Fin 2, (lcmUpto ((![2, 0] : Fin 2 → ℕ) j * n + 0) : ℚ))
      = (lcmUpto (2 * n) : ℚ) := by
    rw [Fin.prod_univ_two]; simp [lcmUpto]
  rw [hprod, coeff_B2, Nat.cast_one, one_mul, pow_zero, one_mul]
  exact hz

theorem b3_denom : HasDenomType 1 ![2, 0] B3 := by
  refine ⟨1, 0, by norm_num, fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := Submission.CDT.PureDenom.int_lcmUpto_mul_n_mul_b3 n
  refine ⟨z, ?_⟩
  have hprod : (∏ j : Fin 2, (lcmUpto ((![2, 0] : Fin 2 → ℕ) j * n + 0) : ℚ))
      = (lcmUpto (2 * n) : ℚ) := by
    rw [Fin.prod_univ_two]; simp [lcmUpto]
  rw [hprod, coeff_B3, Nat.cast_one, one_mul, pow_one]
  rw [mul_comm ((n : ℚ)) ((lcmUpto (2 * n) : ℚ))]
  exact hz

theorem b5_denom : HasDenomType 0 ![2, 2] B5 := by
  refine ⟨1, 0, by norm_num, fun n hn => ?_⟩
  obtain ⟨z1, hz1⟩ := Submission.CDT.PureDenom.int_lcmUpto_mul_two_n_sub_one_mul_b5 n
  have hz1' : (lcmUpto (2 * n) : ℚ) * (((2 * n - 1 : ℕ)) : ℚ) * pb5 n = (z1 : ℚ) := hz1
  obtain ⟨q, hq⟩ := dvd_lcmUpto (k := 2 * n - 1) (N := 2 * n) (by omega) (by omega)
  refine ⟨(q : ℤ) * z1, ?_⟩
  have hprod : (∏ j : Fin 2, (lcmUpto ((![2, 2] : Fin 2 → ℕ) j * n + 0) : ℚ))
      = (lcmUpto (2 * n) : ℚ) ^ 2 := by
    rw [Fin.prod_univ_two]; simp [lcmUpto]; ring
  rw [hprod, coeff_B5]
  simp only [Nat.cast_one, one_mul, pow_zero]
  have hL : (lcmUpto (2 * n) : ℚ) = (((2 * n - 1 : ℕ)) : ℚ) * (q : ℚ) := by
    rw [hq]; push_cast; ring
  have key : ((lcmUpto (2 * n) : ℚ)) ^ 2 * pb5 n
      = (q : ℚ) * ((lcmUpto (2 * n) : ℚ) * (((2 * n - 1 : ℕ)) : ℚ) * pb5 n) := by
    rw [hL]; ring
  rw [key, hz1']
  push_cast
  ring

theorem b6_denom : HasDenomType 1 ![2, 2] B6 := by
  refine ⟨1, 0, by norm_num, fun n hn => ?_⟩
  obtain ⟨z1, hz1⟩ := Submission.CDT.PureDenom.int_lcmUpto_mul_n_sq_mul_b6 n
  have hz1' : (lcmUpto (2 * n) : ℚ) * (n : ℚ) ^ 2 * pb6 n = (z1 : ℚ) := hz1
  obtain ⟨q, hq⟩ := dvd_lcmUpto (k := n) (N := 2 * n) hn (by omega)
  refine ⟨(q : ℤ) * z1, ?_⟩
  have hprod : (∏ j : Fin 2, (lcmUpto ((![2, 2] : Fin 2 → ℕ) j * n + 0) : ℚ))
      = (lcmUpto (2 * n) : ℚ) ^ 2 := by
    rw [Fin.prod_univ_two]; simp [lcmUpto]; ring
  rw [hprod, coeff_B6]
  simp only [Nat.cast_one, one_mul, pow_one]
  have hL : (lcmUpto (2 * n) : ℚ) = (n : ℚ) * (q : ℚ) := by
    rw [hq]; push_cast; ring
  have key : (n : ℚ) * ((lcmUpto (2 * n) : ℚ)) ^ 2 * pb6 n
      = (q : ℚ) * ((lcmUpto (2 * n) : ℚ) * (n : ℚ) ^ 2 * pb6 n) := by
    rw [hL]; ring
  rw [key, hz1']
  push_cast
  ring

theorem b7_denom : HasDenomType 1 ![2, 2] B7 := by
  obtain ⟨K, c, hK, h4⟩ := b4_denom
  refine ⟨K, c, hK, fun n hn => ?_⟩
  obtain ⟨a, ha⟩ := h4 n hn
  refine ⟨a, ?_⟩
  simp only [pow_one]
  rw [coeff_B7, if_neg (by omega : ¬ n = 0)]
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have h1 : (↑K * (n : ℚ) * ∏ j : Fin 2, (lcmUpto ((![2, 2] : Fin 2 → ℕ) j * n + c) : ℚ))
        * (PowerSeries.coeff n B4 / (n : ℚ))
      = (↑K * ∏ j : Fin 2, (lcmUpto ((![2, 2] : Fin 2 → ℕ) j * n + c) : ℚ))
        * PowerSeries.coeff n B4 := by
    have h2 : (n : ℚ) * (PowerSeries.coeff n B4 / (n : ℚ)) = PowerSeries.coeff n B4 := by
      rw [mul_comm]; exact div_mul_cancel₀ _ hn0
    linear_combination (↑K * ∏ j : Fin 2,
      (lcmUpto ((![2, 2] : Fin 2 → ℕ) j * n + c) : ℚ)) * h2
  rw [h1]
  simp only [pow_zero, one_mul, mul_one] at ha
  exact ha

/-! ## `D`-closure of the span of `B₁,…,B₇` -/

noncomputable def dq : Polynomial ℚ :=
  Polynomial.C 2 * Polynomial.X * (Polynomial.C 4 - Polynomial.X)

lemma dq_ne_zero : dq ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval (1 : ℚ)) h
  simp only [Polynomial.eval_zero] at this
  simp [dq] at this
  norm_num at this

noncomputable def dA (i j : Fin 7) : Polynomial ℚ :=
  if (i : ℕ) = 0 then 0
  else if (i : ℕ) = 1 then (if (j : ℕ) = 0 then 2 * Polynomial.X ^ 2
    else if (j : ℕ) = 1 then 4 - 2 * Polynomial.X else 0)
  else if (i : ℕ) = 2 then (if (j : ℕ) = 0 then 4 * Polynomial.X
    else if (j : ℕ) = 1 then -2 else 0)
  else if (i : ℕ) = 3 then (if (j : ℕ) = 0 then -4 * Polynomial.X * (4 - Polynomial.X)
    else if (j : ℕ) = 1 then 2 * (4 - Polynomial.X)
    else if (j : ℕ) = 3 then 2 * (2 - Polynomial.X) else 0)
  else if (i : ℕ) = 4 then (if (j : ℕ) = 0 then 4 * Polynomial.X
    else if (j : ℕ) = 1 then -2
    else if (j : ℕ) = 4 then 4 - Polynomial.X else 0)
  else if (i : ℕ) = 5 then (if (j : ℕ) = 2 then 2 * (4 - Polynomial.X) else 0)
  else (if (j : ℕ) = 3 then 2 * (4 - Polynomial.X) else 0)

lemma dq_coe : ((dq : Polynomial ℚ) : PowerSeries ℚ) = 2 * (X : PowerSeries ℚ) * (4 - X) := by
  simp only [dq, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_C, Polynomial.coe_X]
  rfl

private lemma coe2 : (((2 : Polynomial ℚ)) : PowerSeries ℚ) = (2 : PowerSeries ℚ) := by
  rw [show ((2 : Polynomial ℚ)) = Polynomial.C 2 from rfl, Polynomial.coe_C]; rfl
private lemma coe4 : (((4 : Polynomial ℚ)) : PowerSeries ℚ) = (4 : PowerSeries ℚ) := by
  rw [show ((4 : Polynomial ℚ)) = Polynomial.C 4 from rfl, Polynomial.coe_C]; rfl
private lemma coen2 : (((-2 : Polynomial ℚ)) : PowerSeries ℚ) = -(2 : PowerSeries ℚ) := by
  rw [Polynomial.coe_neg, coe2]
private lemma coen4 : (((-4 : Polynomial ℚ)) : PowerSeries ℚ) = -(4 : PowerSeries ℚ) := by
  rw [Polynomial.coe_neg, coe4]

private lemma pB0 : pureB (0 : Fin 7) = B1 := rfl
private lemma pB1 : pureB (1 : Fin 7) = B2 := rfl
private lemma pB2 : pureB (2 : Fin 7) = B3 := rfl
private lemma pB3 : pureB (3 : Fin 7) = B4 := rfl
private lemma pB4 : pureB (4 : Fin 7) = B5 := rfl
private lemma pB5 : pureB (5 : Fin 7) = B6 := rfl
private lemma pB6 : pureB (6 : Fin 7) = B7 := rfl

theorem dclosed : DClosed pureB := by
  refine ⟨dq, dq_ne_zero, dA, ?_⟩
  intro i
  fin_cases i
  · change (dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B1
      = ∑ j : Fin 7, (((dA (0 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6, B1, PowerSeries.derivative_one,
      Polynomial.coe_zero, zero_mul, mul_zero, add_zero, zero_add]
    norm_num
  · change (dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B2
      = ∑ j : Fin 7, (((dA (1 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [dq_coe]
    linear_combination relation_B2
  · change (dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B3
      = ∑ j : Fin 7, (((dA (2 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [dq_coe]
    linear_combination relation_B3
  · change (dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B4
      = ∑ j : Fin 7, (((dA (3 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [dq_coe]
    linear_combination relation_B4
  · change (dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B5
      = ∑ j : Fin 7, (((dA (4 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [dq_coe]
    linear_combination relation_B5
  · change (dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B6
      = ∑ j : Fin 7, (((dA (5 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [dq_coe]
    linear_combination relation_B6
  · change (dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B7
      = ∑ j : Fin 7, (((dA (6 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [dq_coe]
    linear_combination relation_B7

/-! ## Assembly -/

theorem pure_facts : PureFacts :=
  ⟨b1_denom, b2_denom, b3_denom, b4_denom, b5_denom, b6_denom, b7_denom, dclosed⟩

end Work.Pure
