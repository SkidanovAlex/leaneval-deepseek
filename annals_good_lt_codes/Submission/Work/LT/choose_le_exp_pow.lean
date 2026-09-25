import Mathlib

namespace Work.LT

/-- Factorial lower bound: `(w/e)^w ≤ w!`, obtained from Stirling's lower bound. -/
lemma div_exp_pow_le_factorial (w : ℕ) :
    ((w : ℝ) / Real.exp 1) ^ w ≤ (w.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · have hsqrt : (1:ℝ) ≤ Real.sqrt (2 * Real.pi * w) := by
      rw [Real.one_le_sqrt]
      have hw1 : (1:ℝ) ≤ w := by exact_mod_cast hw
      have hpi : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      nlinarith [Real.pi_pos]
    have hstir := Stirling.le_factorial_stirling w
    calc ((w : ℝ) / Real.exp 1) ^ w
        = 1 * ((w : ℝ) / Real.exp 1) ^ w := by ring
      _ ≤ Real.sqrt (2 * Real.pi * w) * ((w : ℝ) / Real.exp 1) ^ w :=
          mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ ≤ (w.factorial : ℝ) := hstir

/-- `(n choose w) ≤ (n e / w)^w` for `w > 0`. -/
theorem choose_le_exp_pow (n w : ℕ) (hw : 0 < w) :
    (n.choose w : ℝ) ≤ ((n : ℝ) * Real.exp 1 / w) ^ w := by
  have hfact := div_exp_pow_le_factorial w
  have hchoose : (n.choose w : ℝ) ≤ (n:ℝ)^w / (w.factorial : ℝ) :=
    Nat.choose_le_pow_div w n
  refine hchoose.trans ?_
  have hstep : (n:ℝ)^w / (w.factorial : ℝ) ≤ (n:ℝ)^w / ((w:ℝ)/Real.exp 1)^w :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hfact
  refine hstep.trans (le_of_eq ?_)
  rw [← div_pow]
  congr 1
  field_simp

end Work.LT
