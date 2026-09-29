import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.dvd_lcmUpto_mul_choose_two_mul_self
import Submission.Commons.NumberTheory.Chebyshev.dvd_lcmUpto_fact_two_mul_sub_one_mul_fact_div
import Submission.Commons.NumberTheory.Chebyshev.dvd_lcmUpto_mul_choose_two_mul_sub_one

/-!
# Denominator types of the pure functions `B_2, B_3, B_5, B_6`

Lemma `bdenominators` of Calegari--Dimitrov--Tang (arXiv:2408.15403), §"Pure functions", states the
denominator types of the seven functions `B_i(y)`:

| `i` | coefficient of `y^n` | denominator type |
|---|---|---|
| 1 | `1` | trivial |
| 2 | `2·(n-2)!·n!/(2n)!` | `[1..2n]` |
| 3 | `(n-1)!^2/(2n)!` | `[1..2n]·n` |
| 4 | (symmetrised `Li_2`) | `[1..2n]^2` |
| 5 | `(n-1)!^2/((2n-1)!(2n-1))` | `[1..2n]·(2n-1)` |
| 6 | `(n-1)!^2/(n(2n)!)` | `[1..2n]·n^2` |
| 7 | `∫ B_4/y` | `[1..2n]^2·n` |

Here `[1..2n]` denotes `lcmUpto (2n)`.  This module formalises the four cases (`i = 2,3,5,6`) whose
proof the paper describes as a "direct computation" from the explicit factorial formula for the
coefficients; the cases `i = 4, 7` come from the Eichler-integral/`etalecover` input
(weight-zero modularity) and are not formalised here.

The three arithmetic inputs, all in the commons:
* `Commons.NumberTheory.Chebyshev.dvd_lcmUpto_mul_choose_two_mul_self`  : `n·C(2n,n) ∣ lcmUpto (2n)`;
* `Commons.NumberTheory.Chebyshev.dvd_lcmUpto_mul_choose_two_mul_sub_one` : `n·C(2n-1,n-1) ∣ lcmUpto (2n)`;
* `Commons.NumberTheory.Chebyshev.dvd_lcmUpto_fact_two_mul_sub_one_mul_fact_div` :
  `lcmUpto (2n)·(n-2)!(n-1)!/(2n-1)! ∈ ℤ`, which is the case `i = 2`.
-/

open scoped BigOperators

namespace Submission.CDT.PureDenom

lemma factorial_two_mul (n : ℕ) :
    (Nat.factorial (2*n) : ℚ) = ((Nat.factorial n : ℚ))^2 * (Nat.choose (2*n) n : ℚ) := by
  have h : Nat.choose (2*n) n * Nat.factorial n * Nat.factorial (2*n - n) = Nat.factorial (2*n) :=
    Nat.choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left n (by norm_num : 0 < 2))
  have h2 : 2*n - n = n := by omega
  rw [h2] at h
  have : (Nat.factorial (2*n) : ℚ)
      = (Nat.choose (2*n) n : ℚ) * (Nat.factorial n : ℚ) * (Nat.factorial n : ℚ) := by
    rw [← h]; push_cast; ring
  rw [this]; ring

lemma factorial_succ_cast (n : ℕ) (hn : 0 < n) :
    (Nat.factorial n : ℚ) = (n : ℚ) * (Nat.factorial (n-1) : ℚ) := by
  have h2 : ((n - 1 : ℕ) : ℚ) + 1 = (n : ℚ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]; ring
  conv_lhs => rw [show n = n - 1 + 1 by omega, Nat.factorial_succ]
  push_cast
  rw [h2]

lemma factorial_two_mul_eq (n : ℕ) (hn : 1 ≤ n) :
    (Nat.factorial (2*n) : ℚ) = (2*n : ℚ) * (Nat.factorial (2*n-1) : ℚ) := by
  have h2 : ((2*n - 1 : ℕ) : ℚ) + 1 = ((2*n : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*n), Nat.cast_one]; push_cast; ring
  conv_lhs => rw [show 2*n = 2*n - 1 + 1 by omega, Nat.factorial_succ]
  push_cast
  rw [h2]
  push_cast
  ring

noncomputable def b2 (n : ℕ) : ℚ :=
  if n < 2 then 0 else 2 * (Nat.factorial (n-2) : ℚ) * (Nat.factorial n : ℚ) / (Nat.factorial (2*n) : ℚ)
noncomputable def b3 (n : ℕ) : ℚ :=
  if n = 0 then 0 else (Nat.factorial (n-1) : ℚ)^2 / (Nat.factorial (2*n) : ℚ)
noncomputable def b5 (n : ℕ) : ℚ :=
  if n = 0 then 0 else (Nat.factorial (n-1) : ℚ)^2 / ((Nat.factorial (2*n-1) : ℚ) * (((2*n-1 : ℕ)) : ℚ))
noncomputable def b6 (n : ℕ) : ℚ :=
  if n = 0 then 0 else (Nat.factorial (n-1) : ℚ)^2 / ((n : ℚ) * (Nat.factorial (2*n) : ℚ))

lemma n_mul_b3_eq (n : ℕ) (hn : 1 ≤ n) :
    (n:ℚ) * b3 n = 1 / ((n:ℚ) * (Nat.choose (2*n) n : ℚ)) := by
  rw [b3, if_neg (by omega : ¬ n = 0)]
  rw [factorial_two_mul n, factorial_succ_cast n (by omega)]
  have hn0 : (n:ℚ) ≠ 0 := by positivity
  have hC : (Nat.choose (2*n) n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2*n)).ne'
  have hfn : (Nat.factorial (n-1) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-1)
  field_simp

lemma n_sq_mul_b6_eq (n : ℕ) (hn : 1 ≤ n) :
    (n:ℚ)^2 * b6 n = 1 / ((n:ℚ) * (Nat.choose (2*n) n : ℚ)) := by
  rw [b6, if_neg (by omega : ¬ n = 0)]
  rw [factorial_two_mul n, factorial_succ_cast n (by omega)]
  have hn0 : (n:ℚ) ≠ 0 := by positivity
  have hC : (Nat.choose (2*n) n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2*n)).ne'
  have hfn : (Nat.factorial (n-1) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-1)
  field_simp

lemma two_n_sub_one_mul_b5_eq (n : ℕ) (hn : 1 ≤ n) :
    (((2*n-1 : ℕ)) : ℚ) * b5 n = 1 / ((n:ℚ) * (Nat.choose (2*n-1) (n-1) : ℚ)) := by
  rw [b5, if_neg (by omega : ¬ n = 0)]
  have hchoose : Nat.choose (2*n-1) (n-1) * Nat.factorial (n-1) * Nat.factorial (2*n-1 - (n-1))
      = Nat.factorial (2*n-1) :=
    Nat.choose_mul_factorial_mul_factorial (by omega : n-1 ≤ 2*n-1)
  have h2 : 2*n-1 - (n-1) = n := by omega
  rw [h2] at hchoose
  have hfac : (Nat.factorial (2*n-1) : ℚ)
      = (Nat.choose (2*n-1) (n-1) : ℚ) * (Nat.factorial (n-1) : ℚ) * (Nat.factorial n : ℚ) := by
    rw [← hchoose]; push_cast; ring
  rw [hfac, factorial_succ_cast n (by omega)]
  have hn0 : (n:ℚ) ≠ 0 := by positivity
  have hC : (Nat.choose (2*n-1) (n-1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n-1 ≤ 2*n-1)).ne'
  have hfn : (Nat.factorial (n-1) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-1)
  have h21 : (((2*n-1 : ℕ)) : ℚ) ≠ 0 := by
    exact_mod_cast (show 2*n-1 ≠ 0 by omega)
  field_simp

lemma b2_eq (n : ℕ) (hn : 2 ≤ n) :
    b2 n = (Nat.factorial (n-2) : ℚ) * (Nat.factorial (n-1) : ℚ) / (Nat.factorial (2*n-1) : ℚ) := by
  rw [b2, if_neg (by omega : ¬ n < 2)]
  rw [factorial_two_mul_eq n (by omega), factorial_succ_cast n (by omega)]
  have hn0 : (n:ℚ) ≠ 0 := by positivity
  have h2n : (2*n : ℚ) ≠ 0 := by positivity
  have hf21 : (Nat.factorial (2*n-1) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*n-1)
  field_simp

/-- `lcmUpto (2n) · (n-2)! (n-1)! / (2n-1)! ∈ ℤ` (the case `i = 2` of the table). -/
lemma lcmUpto_mul_fact_div_fact (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (Nat.lcmUpto (2 * n) : ℚ) * ((((n - 2).factorial : ℚ)) * (((n - 1).factorial : ℚ)))
        / (((2 * n - 1).factorial : ℚ)) = (z : ℚ) :=
  Commons.NumberTheory.Chebyshev.dvd_lcmUpto_fact_two_mul_sub_one_mul_fact_div n hn

/-- `lcmUpto (2n) / (n · C(2n-1,n-1)) ∈ ℤ`. -/
lemma lcmUpto_div_choose_sub_one (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (Nat.lcmUpto (2*n) : ℚ) / ((n:ℚ) * (Nat.choose (2*n-1) (n-1) : ℚ)) = (z : ℚ) := by
  obtain ⟨k, hk⟩ := Commons.NumberTheory.Chebyshev.dvd_lcmUpto_mul_choose_two_mul_sub_one n hn
  refine ⟨k, ?_⟩
  rw [hk]
  push_cast
  have hn0 : (n:ℚ) ≠ 0 := by positivity
  have hC : (Nat.choose (2*n-1) (n-1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n-1 ≤ 2*n-1)).ne'
  field_simp

/-- `lcmUpto (2n) / (n · C(2n,n)) ∈ ℤ`. -/
lemma lcmUpto_div_choose_self (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (Nat.lcmUpto (2*n) : ℚ) / ((n:ℚ) * (Nat.choose (2*n) n : ℚ)) = (z : ℚ) := by
  obtain ⟨k, hk⟩ := Commons.NumberTheory.Chebyshev.dvd_lcmUpto_mul_choose_two_mul_self n hn
  refine ⟨k, ?_⟩
  rw [hk]
  push_cast
  have hn0 : (n:ℚ) ≠ 0 := by positivity
  have hC : (Nat.choose (2*n) n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2*n)).ne'
  field_simp

theorem int_lcmUpto_mul_b2 (n : ℕ) :
    ∃ z : ℤ, (Nat.lcmUpto (2*n) : ℚ) * b2 n = (z : ℚ) := by
  rcases lt_or_ge n 2 with hn | hn
  · refine ⟨0, ?_⟩
    rw [show b2 n = 0 from by rw [b2, if_pos hn]]; ring
  · obtain ⟨k, hk⟩ := lcmUpto_mul_fact_div_fact n (by omega)
    refine ⟨k, ?_⟩
    rw [b2_eq n hn, ← mul_div_assoc]
    exact hk

theorem int_lcmUpto_mul_n_mul_b3 (n : ℕ) :
    ∃ z : ℤ, (Nat.lcmUpto (2*n) : ℚ) * (n:ℚ) * b3 n = (z : ℚ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; refine ⟨0, ?_⟩; rw [b3, if_pos rfl]; ring
  · obtain ⟨k, hk⟩ := lcmUpto_div_choose_self n hn
    refine ⟨k, ?_⟩
    rw [mul_assoc, n_mul_b3_eq n hn, mul_one_div, hk]

theorem int_lcmUpto_mul_n_sq_mul_b6 (n : ℕ) :
    ∃ z : ℤ, (Nat.lcmUpto (2*n) : ℚ) * (n:ℚ)^2 * b6 n = (z : ℚ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; refine ⟨0, ?_⟩; rw [b6, if_pos rfl]; ring
  · obtain ⟨k, hk⟩ := lcmUpto_div_choose_self n hn
    refine ⟨k, ?_⟩
    rw [mul_assoc, n_sq_mul_b6_eq n hn, mul_one_div, hk]

theorem int_lcmUpto_mul_two_n_sub_one_mul_b5 (n : ℕ) :
    ∃ z : ℤ, (Nat.lcmUpto (2*n) : ℚ) * (((2*n-1 : ℕ)) : ℚ) * b5 n = (z : ℚ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; refine ⟨0, ?_⟩; rw [b5, if_pos rfl]; ring
  · obtain ⟨k, hk⟩ := lcmUpto_div_choose_sub_one n hn
    refine ⟨k, ?_⟩
    rw [mul_assoc, two_n_sub_one_mul_b5_eq n hn, mul_one_div, hk]

end Submission.CDT.PureDenom
