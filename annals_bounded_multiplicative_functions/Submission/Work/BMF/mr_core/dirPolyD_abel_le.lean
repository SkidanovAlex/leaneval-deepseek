import Mathlib
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_direct.window_abel_prefix
import Submission.Work.BMF.mr_direct.window_sum_cpow_eq
import Submission.Work.BMF.mr_direct.window_reindex
import Submission.Work.BMF.mr_direct.window_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

open scoped BigOperators

/-- Purely numerical core of the Abel estimate for the window `[Y, 3Y]`.

With `a = ⌊3Y⌋₊` and `b = ⌈Y⌉₊` one has, for `Y ≥ 16`,
`(a + (b - 1)) · (1/a + 1/b) ≤ 9`.  Since `a ≈ 3Y ≈ 3b`, the true value is about
`(3+1)²/3 = 16/3`, so the constant `9` has comfortable room: `2b - 4 ≤ a ≤ 3b` and `b ≥ 16`
make `(a + b - 1)(a + b) ≤ (4b)(4b+1) = 16b² + 4b ≤ 27b² - 36b ≤ 9ab`. -/
private lemma abel_factor_three_le (Y : ℝ) (hY : 16 ≤ Y) :
    (((⌊3 * Y⌋₊ : ℕ) : ℝ) + (((⌈Y⌉₊ : ℕ) : ℝ) - 1)) *
      (1 / ((⌊3 * Y⌋₊ : ℕ) : ℝ) + 1 / ((⌈Y⌉₊ : ℕ) : ℝ)) ≤ 9 := by
  set a : ℝ := ((⌊3 * Y⌋₊ : ℕ) : ℝ) with ha
  set b : ℝ := ((⌈Y⌉₊ : ℕ) : ℝ) with hb
  have hY0 : 0 ≤ Y := by linarith
  have ha_gt : 3 * Y - 1 < a := by
    have := Nat.lt_floor_add_one (3 * Y); rw [← ha] at this; linarith
  have ha_le : a ≤ 3 * Y := by
    have := Nat.floor_le (show (0 : ℝ) ≤ 3 * Y by linarith); rw [← ha] at this; exact this
  have hb_ge : Y ≤ b := by
    have := Nat.le_ceil Y; rw [← hb] at this; exact this
  have hb_lt : b < Y + 1 := by
    have := Nat.ceil_lt_add_one hY0; rw [← hb] at this; exact this
  have hb16 : 16 ≤ b := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have key : (a + (b - 1)) * (1 / a + 1 / b) = ((a + b - 1) * (a + b)) / (a * b) := by
    field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ha_gt, ha_le, hb_ge, hb_lt, hb16, ha0, hb0]

theorem dirPolyD_abel_le (g : ℕ → ℂ) (Y κ t : ℝ) (hY : 16 ≤ Y)
    (hpre : ∀ k : ℕ, ⌈Y⌉₊ - 1 ≤ k → k ≤ ⌊3 * Y⌋₊ →
      ‖∑ j ∈ Finset.Icc 1 k, g j * (j : ℂ) ^ (-(Complex.I * t))‖ ≤ κ * (k : ℝ)) :
    ‖Work.BMF.dirPolyD g Y t‖ ≤ 9 * κ := by
  classical
  have hY2 : (2 : ℝ) ≤ Y := by linarith
  -- `b = ⌈Y⌉₊ ≥ 16`
  have hceil16 : 16 ≤ ⌈Y⌉₊ := by
    have h := Nat.le_ceil Y
    have : (16 : ℝ) ≤ ((⌈Y⌉₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have hceil1 : 1 ≤ ⌈Y⌉₊ := le_trans (by norm_num) hceil16
  have hN : 1 ≤ ⌈Y⌉₊ - 1 := by omega
  -- `N = ⌈Y⌉₊ - 1 < ⌊3Y⌋₊ = M`
  have hNM : ⌈Y⌉₊ - 1 < ⌊3 * Y⌋₊ := by
    have hfa : Y ≤ ((⌊3 * Y⌋₊ : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one (3 * Y); linarith
    have hb : ((⌈Y⌉₊ : ℕ) : ℝ) < Y + 1 := Nat.ceil_lt_add_one (by linarith)
    have hsub : ((⌈Y⌉₊ - 1 : ℕ) : ℝ) = ((⌈Y⌉₊ : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub hceil1]; simp
    have : ((⌈Y⌉₊ - 1 : ℕ) : ℝ) < ((⌊3 * Y⌋₊ : ℕ) : ℝ) := by rw [hsub]; linarith
    exact_mod_cast this
  -- `κ ≥ 0`, from `hpre` at `k = ⌈Y⌉₊ - 1`
  have hK : 0 ≤ κ := by
    have hk := hpre (⌈Y⌉₊ - 1) le_rfl (le_of_lt hNM)
    have hpos : 0 < ((⌈Y⌉₊ - 1 : ℕ) : ℝ) := by
      have : 0 < ⌈Y⌉₊ - 1 := by omega
      exact_mod_cast this
    have h1 : 0 ≤ κ * ((⌈Y⌉₊ - 1 : ℕ) : ℝ) := le_trans (norm_nonneg _) hk
    by_contra hlt
    have hlt' : κ < 0 := not_le.mp hlt
    nlinarith [h1, hpos]
  -- reindex the window `[Y, 3Y]` and apply Abel summation with the weight `1/n`
  have habel := Work.BMF.mr_direct.window_abel_prefix
    (fun n => g n * (n : ℂ) ^ (-(Complex.I * t))) κ (⌈Y⌉₊ - 1) ⌊3 * Y⌋₊ hK hN hNM
    (fun k h1 h2 => hpre k h1 h2)
  unfold Work.BMF.dirPolyD
  rw [Work.BMF.mr_direct.window_sum_cpow_eq g Y t hY2]
  refine le_trans habel ?_
  have hsub : ((⌈Y⌉₊ - 1 : ℕ) : ℝ) = ((⌈Y⌉₊ : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub hceil1]; simp
  have hadd1 : (⌈Y⌉₊ - 1 + 1 : ℕ) = ⌈Y⌉₊ := Nat.sub_add_cancel hceil1
  rw [hsub, hadd1]
  calc κ * (((⌊3 * Y⌋₊ : ℕ) : ℝ) + (((⌈Y⌉₊ : ℕ) : ℝ) - 1)) *
        (1 / ((⌊3 * Y⌋₊ : ℕ) : ℝ) + 1 / ((⌈Y⌉₊ : ℕ) : ℝ))
      = κ * ((((⌊3 * Y⌋₊ : ℕ) : ℝ) + (((⌈Y⌉₊ : ℕ) : ℝ) - 1)) *
        (1 / ((⌊3 * Y⌋₊ : ℕ) : ℝ) + 1 / ((⌈Y⌉₊ : ℕ) : ℝ))) := by ring
    _ ≤ κ * 9 := mul_le_mul_of_nonneg_left (abel_factor_three_le Y hY) hK
    _ = 9 * κ := by ring

end Work.BMF.mr_core
