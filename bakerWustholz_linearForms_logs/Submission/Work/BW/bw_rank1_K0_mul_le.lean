import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For `n, d ≥ 1`: `3·d·((64nd)^{n-1}·n!/2^{n-1}) ≤ C(n,d)·log 2` where
`C(n,d) = 18(n+1)! n^{n+1} (32d)^{n+2} log(2nd)`.
Proof sketch: `(64nd)^{n-1}/2^{n-1} = (32nd)^{n-1}`, so the goal becomes
`3d(32nd)^{n-1}n! ≤ 18(n+1)!n^{n+1}(32d)^{n+2}log(2nd)log2`; divide by the positive common factor
`3d·(32nd)^{n-1}·n!` to reduce to `1 ≤ 6(n+1)n²·32³·d²·log(2nd)·log 2`, which holds since
`log(2nd) ≥ log 2 ≥ 2/3` (`Real.log_two_gt_d9`) and `(n+1) ≥ 2`, `n ≥ 1`, `d ≥ 1`. -/
theorem bw_rank1_K0_mul_le (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    3 * (d : ℝ) * ((64 * n * d : ℝ) ^ (n - 1) * ((n.factorial : ℝ) / 2 ^ (n - 1))) ≤
      BakerWustholz.C n d * Real.log 2 := by
  -- Step 1: `(64nd)^{n-1}/2^{n-1} = (32nd)^{n-1}`.
  have hL : 3 * (d : ℝ) * ((64 * n * d : ℝ) ^ (n - 1) * ((n.factorial : ℝ) / 2 ^ (n - 1)))
      = 3 * (d : ℝ) * ((32 * n * d : ℝ) ^ (n - 1) * (n.factorial : ℝ)) := by
    have h64 : (64 * n * d : ℝ) = 2 * (32 * n * d : ℝ) := by ring
    rw [h64, mul_pow]
    have h2 : (2 : ℝ) ^ (n - 1) ≠ 0 := by positivity
    field_simp
  -- Step 2: the residual factor `F = 6(n+1)n²32³d² log(2nd) log 2` is at least `1`.
  have hF : (1 : ℝ) ≤
      6 * ((n : ℝ) + 1) * (n : ℝ) ^ 2 * 32 ^ 3 * (d : ℝ) ^ 2 * Real.log (2 * n * d) *
        Real.log 2 := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hn1 : (2 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hnR]
    have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith [hdR]
    have h2nd : (2 : ℝ) ≤ 2 * (n : ℝ) * (d : ℝ) := by nlinarith
    have hlog : (2 / 3 : ℝ) ≤ Real.log (2 * n * d) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2nd
      have h2 := Real.log_two_gt_d9
      linarith
    have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by
      have h2 := Real.log_two_gt_d9
      linarith
    calc (1 : ℝ) ≤ 6 * 2 * 1 * 32 ^ 3 * 1 * (2 / 3) * (2 / 3) := by norm_num
      _ ≤ 6 * ((n : ℝ) + 1) * (n : ℝ) ^ 2 * 32 ^ 3 * (d : ℝ) ^ 2 *
            Real.log (2 * n * d) * Real.log 2 := by gcongr
  -- Step 3: the algebraic identity `P · F = C(n,d) · log 2`.
  have hPF : 3 * (d : ℝ) * ((32 * n * d : ℝ) ^ (n - 1) * (n.factorial : ℝ)) *
        (6 * ((n : ℝ) + 1) * (n : ℝ) ^ 2 * 32 ^ 3 * (d : ℝ) ^ 2 * Real.log (2 * n * d) *
          Real.log 2)
      = BakerWustholz.C n d * Real.log 2 := by
    have key : (n : ℝ) ^ (n + 1) * (32 * (d : ℝ)) ^ (n + 2) =
        (32 * n * d : ℝ) ^ (n - 1) * ((n : ℝ) ^ 2 * (32 * (d : ℝ)) ^ 3) := by
      have e1 : n + 1 = (n - 1) + 2 := by omega
      have e2 : n + 2 = (n - 1) + 3 := by omega
      rw [e1, pow_add, e2, pow_add]
      rw [show (32 * n * d : ℝ) = (n : ℝ) * (32 * (d : ℝ)) by ring, mul_pow]
      ring
    have hmul : (18 : ℝ) * ((n + 1).factorial : ℝ) * (n : ℝ) ^ (n + 1) *
          (32 * (d : ℝ)) ^ (n + 2)
        = (18 : ℝ) * ((n + 1).factorial : ℝ) *
            ((32 * n * d : ℝ) ^ (n - 1) * ((n : ℝ) ^ 2 * (32 * (d : ℝ)) ^ 3)) := by
      rw [show (18 : ℝ) * ((n + 1).factorial : ℝ) * (n : ℝ) ^ (n + 1) *
              (32 * (d : ℝ)) ^ (n + 2)
            = 18 * ((n + 1).factorial : ℝ) *
              ((n : ℝ) ^ (n + 1) * (32 * (d : ℝ)) ^ (n + 2)) by ring,
        key]
    rw [BakerWustholz.C, hmul, Nat.factorial_succ]
    push_cast
    ring
  rw [hL, ← hPF]
  exact le_mul_of_one_le_right (by positivity) hF

end Work.BW
