import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The number of integers in `[x, x + h]` (with `0 ≤ x`, `0 ≤ h`) is at most `h + 1`. -/
lemma natIcc_card_nat_le (x h : ℝ) (hx : 0 ≤ x) (hh : 0 ≤ h) :
    ((natIcc x (x + h)).card : ℝ) ≤ h + 1 := by
  have hb : 0 ≤ x + h := by linarith
  have hle : ((⌊x + h⌋₊ : ℕ) : ℝ) ≤ (⌈x⌉₊ : ℝ) + h := by
    have h1 : ((⌊x + h⌋₊ : ℕ) : ℝ) ≤ x + h := Nat.floor_le hb
    have h2 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    linarith
  rw [natIcc, Nat.card_Icc]
  by_cases hc : ⌈x⌉₊ ≤ ⌊x + h⌋₊ + 1
  · rw [Nat.cast_sub hc]; push_cast; linarith
  · rw [Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hc))]
    simp only [Nat.cast_zero]
    linarith

/-- `‖(1/h : ℂ)‖ = 1/h` for `0 ≤ h`. -/
lemma norm_one_div_ofReal (h : ℝ) (hh : 0 ≤ h) : ‖(1 / h : ℂ)‖ = 1 / h := by
  have heq : (1 / h : ℂ) = ((1 / h : ℝ) : ℂ) := by push_cast; ring
  rw [heq, show ‖((1 / h : ℝ) : ℂ)‖ = |1 / h| by simp]
  exact abs_of_nonneg (div_nonneg zero_le_one hh)

theorem norm_window_avg_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (x h : ℝ) (hx : 0 ≤ x) (hh : 1 ≤ h) :
    ‖(1 / h) * (∑ n ∈ Work.BMF.natIcc x (x + h), a n)‖ ≤ 2 := by
  have hhpos : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hh0 : 0 ≤ h := le_of_lt hhpos
  have hcoef : ‖(1 / h : ℂ)‖ = 1 / h := norm_one_div_ofReal h hh0
  have hsum : ‖∑ n ∈ natIcc x (x + h), a n‖ ≤ ((natIcc x (x + h)).card : ℝ) := by
    calc ‖∑ n ∈ natIcc x (x + h), a n‖
        ≤ ∑ n ∈ natIcc x (x + h), ‖a n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ natIcc x (x + h), (1 : ℝ) := Finset.sum_le_sum (fun n _ => ha n)
      _ = ((natIcc x (x + h)).card : ℝ) := by simp
  have hcard : ((natIcc x (x + h)).card : ℝ) ≤ h + 1 := natIcc_card_nat_le x h hx hh0
  calc ‖(1 / h) * (∑ n ∈ natIcc x (x + h), a n)‖
      = (1 / h) * ‖∑ n ∈ natIcc x (x + h), a n‖ := by rw [norm_mul, hcoef]
    _ ≤ (1 / h) * ((natIcc x (x + h)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg zero_le_one hh0)
    _ ≤ (1 / h) * (h + 1) :=
        mul_le_mul_of_nonneg_left hcard (div_nonneg zero_le_one hh0)
    _ = 1 + 1 / h := by field_simp
    _ ≤ 2 := by
        have h1 : 1 / h ≤ 1 := by
          have := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hh
          simpa using this
        linarith

end Work.BMF
