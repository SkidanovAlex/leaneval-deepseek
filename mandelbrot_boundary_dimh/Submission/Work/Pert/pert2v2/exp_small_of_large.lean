import Mathlib
import Submission.Work.Pert.pert2v2.steps

namespace Work.Pert.pert2v2

theorem exp_small_of_large {M κ H C : ℝ} (hM : 0 < M) (hκ : 0 < κ)
    (hC : 200 * max 1 M / κ ≤ C) (hCH : C ≤ H) :
    M * Real.exp (-(κ * H / 2)) ≤ 1 / 64 := by
  -- Step 1: `C ≥ 200 * max 1 M / κ` gives `100 * max 1 M ≤ κ * C / 2 ≤ κ * H / 2`.
  have hkey : (100:ℝ) * max 1 M ≤ κ * H / 2 := by
    have h1 : (100:ℝ) * max 1 M ≤ κ * C / 2 := by
      have hκ2 : (0:ℝ) < κ / 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_left hC hκ2.le
      have hsimp : κ / 2 * (200 * max 1 M / κ) = 100 * max 1 M := by
        field_simp
        ring
      linarith [hmul, hsimp.ge]
    have h2 : κ * C / 2 ≤ κ * H / 2 := by
      have := mul_le_mul_of_nonneg_left hCH (le_of_lt hκ)
      linarith
    linarith
  -- Step 2: monotonicity of `exp` and nonnegativity of `M`.
  have hmono : Real.exp (-(κ * H / 2)) ≤ Real.exp (-(100 * max 1 M)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hstep : M * Real.exp (-(κ * H / 2)) ≤ M * Real.exp (-(100 * max 1 M)) :=
    mul_le_mul_of_nonneg_left hmono (le_of_lt hM)
  -- Step 3: `exp (-100) ≤ 1/64` (from `64 ≤ 101 ≤ exp 100`).
  have hexp64 : Real.exp (-(100:ℝ)) ≤ 1 / 64 := by
    have h64 : (64:ℝ) ≤ Real.exp 100 := by
      have h := Real.add_one_le_exp (100:ℝ)
      linarith
    have h := one_div_le_one_div_of_le (show (0:ℝ) < 64 by norm_num) h64
    simpa [Real.exp_neg, one_div] using h
  -- Step 4: `M * exp (-(100 * max 1 M)) ≤ 1/64`, by cases on `M ≤ 1`.
  have hfin : M * Real.exp (-(100 * max 1 M)) ≤ 1 / 64 := by
    rcases le_or_gt M 1 with h1 | h1
    · -- `max 1 M = 1` and `M ≤ 1`
      rw [max_eq_left h1]
      have hMle : M ≤ (1:ℝ) := h1
      have hthis : M * Real.exp (-(100 * 1)) ≤ 1 * Real.exp (-(100:ℝ)) := by
        have := mul_le_mul_of_nonneg_right hMle (Real.exp_pos (-(100:ℝ))).le
        simpa using this
      calc M * Real.exp (-(100 * 1)) ≤ 1 * Real.exp (-(100:ℝ)) := hthis
        _ = Real.exp (-(100:ℝ)) := by ring
        _ ≤ 1 / 64 := hexp64
    · -- `max 1 M = M` and `64 * M ≤ exp (100 * M)`
      rw [max_eq_right (le_of_lt h1)]
      have hmon : (64:ℝ) * M ≤ Real.exp (100 * M) := by
        have h := Real.add_one_le_exp (100 * M)
        linarith
      have hone : Real.exp (100 * M) * Real.exp (-(100 * M)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc M * Real.exp (-(100 * M))
          = ((64:ℝ) * M * Real.exp (-(100 * M))) / 64 := by ring
        _ ≤ (Real.exp (100 * M) * Real.exp (-(100 * M))) / 64 := by
              apply div_le_div_of_nonneg_right _ (by norm_num)
              exact mul_le_mul_of_nonneg_right hmon (Real.exp_pos _).le
        _ = 1 / 64 := by rw [hone, one_div]
  exact le_trans hstep hfin

end Work.Pert.pert2v2
