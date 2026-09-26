import Mathlib

namespace Work.CKFinal.LineDecay

/-- Auxiliary monotonicity step: for `2 ≤ m`, the sequence
`((k:ℝ)+2)^4 * (81/256)^k` is non-increasing at `m`.
This is the key estimate, equivalent to `81*(m+3)^4 ≤ 256*(m+2)^4`,
which follows from `3*(m+3) ≤ 4*(m+2)`. -/
private lemma E4tail_cnb_step (m : ℕ) (hm : 2 ≤ m) :
    ((m:ℝ)+3)^4 * (81/256:ℝ)^(m+1) ≤ ((m:ℝ)+2)^4 * (81/256:ℝ)^m := by
  rw [pow_succ]
  have hpoly : 81 * ((m:ℝ)+3)^4 ≤ 256 * ((m:ℝ)+2)^4 := by
    have h : 3*((m:ℝ)+3) ≤ 4*((m:ℝ)+2) := by
      have : (2:ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have h4 : (3*((m:ℝ)+3))^4 ≤ (4*((m:ℝ)+2))^4 := pow_le_pow_left₀ (by positivity) h 4
    norm_num [mul_pow] at h4 ⊢
    exact h4
  have hthis : ((m:ℝ)+3)^4 * (81/256) ≤ ((m:ℝ)+2)^4 := by linarith
  calc ((m:ℝ)+3)^4 * ((81/256:ℝ)^m * (81/256))
      = (((m:ℝ)+3)^4 * (81/256)) * (81/256:ℝ)^m := by ring
    _ ≤ ((m:ℝ)+2)^4 * (81/256:ℝ)^m := by
        exact mul_le_mul_of_nonneg_right hthis (by positivity)

theorem E4tail_cnb (n : ℕ) : ((n : ℝ) + 2) ^ 4 * (1 / 4 : ℝ) ^ n ≤ 26 * (64 / 81 : ℝ) ^ n := by
  -- Reduce to the equivalent bound `((n:ℝ)+2)^4 * (81/256)^n ≤ 26`,
  -- using `1/4 = (81/256) * (64/81)`.
  have hmain : ((n:ℝ)+2)^4 * (81/256:ℝ)^n ≤ 26 := by
    rcases lt_or_ge n 2 with hn | hn
    · interval_cases n <;> norm_num
    · refine Nat.le_induction (m := 2) (P := fun k _ => ((k:ℝ)+2)^4 * (81/256:ℝ)^k ≤ 26)
        (by norm_num) ?_ n hn
      intro m hm ih
      have hfin : ((m:ℝ)+3)^4 * (81/256:ℝ)^(m+1) ≤ 26 :=
        (E4tail_cnb_step m hm).trans ih
      rw [show (((m+1 : ℕ) : ℝ) + 2) = (m:ℝ)+3 by push_cast; ring]
      exact hfin
  have h64 : (0:ℝ) ≤ (64/81)^n := by positivity
  calc ((n : ℝ) + 2) ^ 4 * (1 / 4 : ℝ) ^ n
      = ((n:ℝ)+2)^4 * (81/256)^n * (64/81)^n := by
        rw [show (1/4:ℝ) = (81/256)*(64/81) by norm_num, mul_pow]; ring
    _ ≤ 26 * (64 / 81 : ℝ) ^ n := mul_le_mul_of_nonneg_right hmain h64

end Work.CKFinal.LineDecay
