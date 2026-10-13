import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

/-!
# The sharp `log Q` bound

This file proves `Work.WilkiesH.Interp.V2qb.log_QV_sharp`: if `λ = lamV μ g H ≥ 8g+8`, then

`log QV ≤ log 16 + log N1V + bV · log (Kr μ) / (8g+8)`.

The proof has three elementary ingredients.

* `QV = 4·N₁·⌈exp (b·log K / λ)⌉ + 2` (`QV_eq_four`).  Since `b·log K / λ ≥ 0` the exponent is
  `≥ 1`, so `⌈exp y⌉ ≤ 2·exp y`; using `N₁ ≥ 1` this gives `QV ≤ 16·N₁·exp (b·log K / λ)`
  (`QV_le_sixteen`).
* Taking logarithms: `log (16·N₁·exp y) = log 16 + log N₁ + y`.
* Finally `b·log K / λ ≤ b·log K / (8g+8)` because `λ ≥ 8g+8 > 0` and `b·log K ≥ 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilkiesH.Interp.V2qb

open Work.WilkiesH.Interp

/-- `Kr μ = K = 2μ+4` is at least `1`. -/
lemma one_le_Kr (μ : ℕ) : (1 : ℝ) ≤ Kr μ := by
  rw [Kr]
  exact_mod_cast le_of_lt (one_lt_KK μ)

/-- `log (Kr μ) ≥ 0`. -/
lemma log_Kr_nonneg (μ : ℕ) : 0 ≤ Real.log (Kr μ) := Real.log_nonneg (one_le_Kr μ)

/-- `(bV μ g H : ℝ) · log (Kr μ) ≥ 0`. -/
lemma argV_nonneg_all (μ g H : ℕ) :
    0 ≤ ((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) :=
  mul_nonneg (Nat.cast_nonneg _) (log_Kr_nonneg μ)

/-- For `x ≥ 0` the ceiling of `exp x` is at most `2·exp x`. -/
lemma ceil_exp_le_two_mul_exp (x : ℝ) (hx : 0 ≤ x) :
    ((Nat.ceil (Real.exp x) : ℕ) : ℝ) ≤ 2 * Real.exp x := by
  have h1 : ((Nat.ceil (Real.exp x) : ℕ) : ℝ) < Real.exp x + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos x).le
  have h2 : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
  linarith

/-- The ceiling factor `⌈exp (b log K / λ)⌉` of `QV` is at most `2·exp (b log K / λ)`,
provided the exponent is non-negative. -/
lemma ceilQV_le_two_mul_exp (μ g H : ℕ)
    (h : 0 ≤ ((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) / ((lamV μ g H : ℕ) : ℝ)) :
    ((ceilQV μ g H : ℕ) : ℝ) ≤
      2 * Real.exp (((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) / ((lamV μ g H : ℕ) : ℝ)) := by
  have h1 : ((Nat.ceil (Real.exp (((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) /
      ((lamV μ g H : ℕ) : ℝ))) : ℕ) : ℝ) ≤
      2 * Real.exp (((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) / ((lamV μ g H : ℕ) : ℝ)) :=
    ceil_exp_le_two_mul_exp _ h
  simpa only [ceilQV] using h1

/-- `QV = 4 N₁ ⌈exp (b log K / λ)⌉ + 2 ≤ 16 N₁ exp (b log K / λ)` when `λ ≥ 8g+8`. -/
lemma QV_le_sixteen (μ g H : ℕ) (hlam : 8 * g + 8 ≤ lamV μ g H) :
    ((QV μ g H : ℕ) : ℝ) ≤ 16 * ((N1V μ g H : ℕ) : ℝ) *
      Real.exp (((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) / ((lamV μ g H : ℕ) : ℝ)) := by
  have hlpos : 0 < lamV μ g H := by omega
  have harg : 0 ≤ ((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) / ((lamV μ g H : ℕ) : ℝ) :=
    div_nonneg (argV_nonneg_all μ g H) (Nat.cast_nonneg _)
  have hc := ceilQV_le_two_mul_exp μ g H harg
  have hN1 : (1 : ℝ) ≤ ((N1V μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_N1V μ g H
  have hE : (1 : ℝ) ≤ Real.exp (((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) /
      ((lamV μ g H : ℕ) : ℝ)) := Real.one_le_exp harg
  rw [QV_eq_four]
  push_cast
  nlinarith [hc, hN1, hE]

theorem log_QV_sharp (μ g H : ℕ) (hlam : 8 * g + 8 ≤ Work.WilkiesH.Interp.lamV μ g H) :
    Real.log ((Work.WilkiesH.Interp.QV μ g H : ℕ) : ℝ) ≤
      Real.log 16 + Real.log ((Work.WilkiesH.Interp.N1V μ g H : ℕ) : ℝ) +
        ((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) *
          Real.log (Work.WilkiesH.Interp.Kr μ) / (8 * (g : ℝ) + 8) := by
  have hQle := QV_le_sixteen μ g H hlam
  have harg : 0 ≤ ((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) / ((lamV μ g H : ℕ) : ℝ) :=
    div_nonneg (argV_nonneg_all μ g H) (Nat.cast_nonneg _)
  have hQpos : (0 : ℝ) < ((QV μ g H : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (one_le_QV μ g H))
  have hN1pos : (0 : ℝ) < ((N1V μ g H : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (one_le_N1V μ g H))
  have hexppos : (0 : ℝ) < Real.exp (((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) /
      ((lamV μ g H : ℕ) : ℝ)) := Real.exp_pos _
  have hlog := Real.log_le_log hQpos hQle
  have hlogid : Real.log (16 * ((N1V μ g H : ℕ) : ℝ) * Real.exp (((bV μ g H : ℕ) : ℝ) *
        Real.log (Kr μ) / ((lamV μ g H : ℕ) : ℝ)))
      = Real.log 16 + Real.log ((N1V μ g H : ℕ) : ℝ) +
        ((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) / ((lamV μ g H : ℕ) : ℝ) := by
    rw [Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hN1pos)) (ne_of_gt hexppos),
      Real.log_mul (by norm_num) (ne_of_gt hN1pos), Real.log_exp]
  have hlR : 8 * (g : ℝ) + 8 ≤ ((lamV μ g H : ℕ) : ℝ) := by
    have h : ((8 * g + 8 : ℕ) : ℝ) ≤ ((lamV μ g H : ℕ) : ℝ) := by exact_mod_cast hlam
    simpa using h
  have hdiv : ((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) / ((lamV μ g H : ℕ) : ℝ) ≤
      ((bV μ g H : ℕ) : ℝ) * Real.log (Kr μ) / (8 * (g : ℝ) + 8) :=
    div_le_div_of_nonneg_left (argV_nonneg_all μ g H) (by positivity) hlR
  rw [hlogid] at hlog
  linarith [hlog, hdiv]

end Work.WilkiesH.Interp.V2qb
