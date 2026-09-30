import Mathlib
import Submission.Work.BMF.Psi1_local_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BMF

open Real

/-- Pure real-analysis input for `Work.BMF.serTerm_le_of_le`: for every `n : ℕ`,
`2^n * exp (-(log 2)^2 * (max 0 (n-1))^2) ≤ 10 * exp (-1/8)^n`.

For `n = 0, 1, 2, 3` this is checked directly (using `exp (-1/8) ≥ 7/8` and, for `n = 3`,
`exp (-4 (log 2)^2) ≤ exp (-1) ≤ 1/2`).  For `n ≥ 4` one shows
`n log 2 + n/8 ≤ (log 2)^2 (n-1)^2`, taking logarithms of the two sides. -/
theorem exp_quad_decay_aux (n : ℕ) :
    (2 : ℝ) ^ n * Real.exp (-(Real.log 2) ^ 2 * (max 0 ((n : ℝ) - 1)) ^ 2) ≤
      10 * (Real.exp (-(1 / 8 : ℝ))) ^ n := by
  have he : (7 / 8 : ℝ) ≤ Real.exp (-(1 / 8 : ℝ)) := by
    have h := Real.add_one_le_exp (-(1 / 8 : ℝ)); linarith
  have he0 : (0 : ℝ) ≤ Real.exp (-(1 / 8 : ℝ)) := (Real.exp_pos _).le
  have hE2 : (2 / 5 : ℝ) ≤ (Real.exp (-(1 / 8 : ℝ))) ^ 2 := by nlinarith [he, he0]
  have hE3 : (2 / 5 : ℝ) ≤ (Real.exp (-(1 / 8 : ℝ))) ^ 3 := by nlinarith [he, he0, hE2]
  rcases Nat.lt_or_ge n 4 with hn | hn4
  · interval_cases n
    · norm_num
    · norm_num
      linarith
    · norm_num
      have hb : Real.exp (-(Real.log 2) ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (Real.log 2)]
      nlinarith [hb, hE2]
    · norm_num
      have hb : Real.exp (-((Real.log 2) ^ 2 * 4)) ≤ 1 / 2 := by
        have hL : (1 : ℝ) ≤ (Real.log 2) ^ 2 * 4 := by nlinarith [Real.log_two_gt_d9]
        have hm : -((Real.log 2) ^ 2 * 4) ≤ -(1 : ℝ) := by linarith
        calc Real.exp (-((Real.log 2) ^ 2 * 4)) ≤ Real.exp (-(1 : ℝ)) := Real.exp_le_exp.mpr hm
          _ = (Real.exp (1 : ℝ))⁻¹ := Real.exp_neg 1
          _ ≤ 1 / 2 := by
              have h := one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num)
                (le_of_lt Real.exp_one_gt_two)
              simpa [one_div] using h
      nlinarith [hb, hE3]
  · have hm : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hm0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
    have hL23 : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hL0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hL38 : (3 : ℝ) / 8 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hsq : 2 * (n : ℝ) ≤ ((n : ℝ) - 1) ^ 2 := by nlinarith [hm, sq_nonneg ((n : ℝ) - 2)]
    have ht2 : (2 : ℝ) / 3 * Real.log 2 ≤ (Real.log 2) ^ 2 := by nlinarith [hL23, hL0]
    have h1 : (2 : ℝ) / 3 * Real.log 2 * (2 * (n : ℝ)) ≤ (Real.log 2) ^ 2 * ((n : ℝ) - 1) ^ 2 :=
      mul_le_mul ht2 hsq (by linarith) (by positivity)
    have h2 : (n : ℝ) * Real.log 2 + (n : ℝ) / 8 ≤ (2 : ℝ) / 3 * Real.log 2 * (2 * (n : ℝ)) := by
      calc (n : ℝ) * Real.log 2 + (n : ℝ) / 8 = (n : ℝ) * (Real.log 2 + 1 / 8) := by ring
        _ ≤ (n : ℝ) * ((4 : ℝ) / 3 * Real.log 2) :=
            mul_le_mul_of_nonneg_left (by linarith [hL38]) hm0
        _ = (2 : ℝ) / 3 * Real.log 2 * (2 * (n : ℝ)) := by ring
    have hkey : (n : ℝ) * Real.log 2 - (Real.log 2) ^ 2 * ((n : ℝ) - 1) ^ 2 ≤ -(n : ℝ) / 8 := by
      linarith [le_trans h2 h1]
    have hmax : max 0 ((n : ℝ) - 1) = (n : ℝ) - 1 := max_eq_right (by linarith)
    have h2n : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
      conv_lhs => rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [← Real.exp_nat_mul]
    have hE : (Real.exp (-(1 / 8 : ℝ))) ^ n = Real.exp (-(n : ℝ) / 8) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hLHS : (2 : ℝ) ^ n * Real.exp (-(Real.log 2) ^ 2 * (max 0 ((n : ℝ) - 1)) ^ 2)
        = Real.exp ((n : ℝ) * Real.log 2 - (Real.log 2) ^ 2 * ((n : ℝ) - 1) ^ 2) := by
      rw [h2n, hmax, ← Real.exp_add]
      congr 1
      ring
    rw [hLHS, hE]
    calc Real.exp ((n : ℝ) * Real.log 2 - (Real.log 2) ^ 2 * ((n : ℝ) - 1) ^ 2)
        ≤ Real.exp (-(n : ℝ) / 8) := Real.exp_le_exp.mpr hkey
      _ ≤ 10 * Real.exp (-(n : ℝ) / 8) := by
          have := Real.exp_pos (-(n : ℝ) / 8); linarith

/-- For `k ≤ j` the block term `serTerm α j k` is bounded by the "short" side decay
`10 * 2^(-jα) * exp(-1/8)^(j-k)`.

Indeed `serTerm α j k = 2^(-kα) * exp (-(log 2)^2 * (max 0 (j-k-1))^2)`, and since `α ≤ 1`,
`2^(-kα) ≤ 2^(-jα) * 2^(j-k)`.  It therefore suffices to bound
`2^(j-k) * exp (-(log 2)^2 * (max 0 (j-k-1))^2)` by `10 * exp(-1/8)^(j-k)`, which is
`Work.BMF.exp_quad_decay_aux`. -/
theorem serTerm_le_of_le (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) {j k : ℕ} (hk : k ≤ j) :
    Work.BMF.serTerm α j k ≤
      10 * (2 : ℝ) ^ (-(j : ℝ) * α) * (Real.exp (-(1 / 8 : ℝ))) ^ (j - k) := by
  set n : ℕ := j - k with hn
  have hcast : (n : ℝ) = (j : ℝ) - (k : ℝ) := by
    rw [hn, Nat.cast_sub hk]
  have hcastk : (k : ℝ) = (j : ℝ) - (n : ℝ) := by rw [hcast]; ring
  have habs : |(j : ℝ) - (k : ℝ)| = (n : ℝ) := by
    have h0 : (0 : ℝ) ≤ (j : ℝ) - (k : ℝ) := by
      have h1 : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hk
      linarith
    rw [abs_of_nonneg h0, ← hcast]
  have hser : Work.BMF.serTerm α j k =
      (2 : ℝ) ^ (-(k : ℝ) * α) *
        Real.exp (-(Real.log 2) ^ 2 * (max 0 ((n : ℝ) - 1)) ^ 2) := by
    rw [Work.BMF.serTerm, habs]
  have step1 : (2 : ℝ) ^ (-(k : ℝ) * α) ≤ (2 : ℝ) ^ (-(j : ℝ) * α) * (2 : ℝ) ^ n := by
    have heq : -(k : ℝ) * α = -(j : ℝ) * α + (n : ℝ) * α := by rw [hcastk]; ring
    rw [heq, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hle : (n : ℝ) * α ≤ (n : ℝ) := by
      have h1 : (n : ℝ) * α ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hα1 hn0
      simpa using h1
    calc (2 : ℝ) ^ ((n : ℝ) * α) ≤ (2 : ℝ) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = (2 : ℝ) ^ n := Real.rpow_natCast 2 n
  calc Work.BMF.serTerm α j k
      = (2 : ℝ) ^ (-(k : ℝ) * α) *
          Real.exp (-(Real.log 2) ^ 2 * (max 0 ((n : ℝ) - 1)) ^ 2) := hser
    _ ≤ ((2 : ℝ) ^ (-(j : ℝ) * α) * (2 : ℝ) ^ n) *
          Real.exp (-(Real.log 2) ^ 2 * (max 0 ((n : ℝ) - 1)) ^ 2) :=
        mul_le_mul_of_nonneg_right step1 (Real.exp_nonneg _)
    _ = (2 : ℝ) ^ (-(j : ℝ) * α) *
          ((2 : ℝ) ^ n * Real.exp (-(Real.log 2) ^ 2 * (max 0 ((n : ℝ) - 1)) ^ 2)) := by ring
    _ ≤ (2 : ℝ) ^ (-(j : ℝ) * α) * (10 * (Real.exp (-(1 / 8 : ℝ))) ^ n) :=
        mul_le_mul_of_nonneg_left (exp_quad_decay_aux n) (Real.rpow_nonneg (by norm_num) _)
    _ = 10 * (2 : ℝ) ^ (-(j : ℝ) * α) * (Real.exp (-(1 / 8 : ℝ))) ^ n := by ring
    _ = 10 * (2 : ℝ) ^ (-(j : ℝ) * α) * (Real.exp (-(1 / 8 : ℝ))) ^ (j - k) := by rw [hn]

end Work.BMF
