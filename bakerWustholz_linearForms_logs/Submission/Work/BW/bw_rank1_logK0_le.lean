import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `log (n!) ≤ n²` for every `n`: since `n! ≤ n^n` (`Nat.factorial_le_pow`) and
`log (n^n) = n log n ≤ n · n`. -/
private lemma log_factorial_le_sq (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hle : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hpos : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h1 : Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
    Real.log_le_log hpos hle
  rw [Real.log_pow] at h1
  have h2 : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self (Nat.cast_nonneg n)
  have h3 : (n : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
  linarith [h1, h3]

/-- For `n, d ≥ 1`, with `K₀ := (64nd)^{n-1} · n!/2^{n-1}`, we have `log K₀ ≤ (n-1)·64nd + n²`.
Proof sketch: `Real.log_mul` + `Real.log_pow` split `log K₀` into `(n-1)log(64nd) + log(n!/2^{n-1})`;
`log(64nd) ≤ 64nd` (`Real.log_le_self`); `log(n!/2^{n-1}) ≤ log(n!)` (`Real.log_le_log`, as `2^{n-1} ≥ 1`);
and `log(n!) = ∑_{i<n} log(i+1) ≤ ∑_{i<n} n = n²` since `i+1 ≤ n` and `log x ≤ x` (`Real.log_le_self`).
Complements `Work.BW.bw_rank1_logK0_num_le`. -/
theorem bw_rank1_logK0_le (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    Real.log ((64 * n * d : ℝ) ^ (n - 1) * ((n.factorial : ℝ) / 2 ^ (n - 1))) ≤
      ((n : ℝ) - 1) * (64 * n * d : ℝ) + (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbase_pos : (0 : ℝ) < (64 * n * d : ℝ) := by nlinarith [hn0, hd0]
  have hA : (0 : ℝ) < (64 * n * d : ℝ) ^ (n - 1) := pow_pos hbase_pos _
  have hnfact : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h2pow : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  have hB : (0 : ℝ) < (n.factorial : ℝ) / 2 ^ (n - 1) := div_pos hnfact h2pow
  rw [Real.log_mul (ne_of_gt hA) (ne_of_gt hB), Real.log_pow]
  have hlogbase : Real.log (64 * n * d : ℝ) ≤ (64 * n * d : ℝ) :=
    Real.log_le_self (le_of_lt hbase_pos)
  have hn1_nonneg : (0 : ℝ) ≤ ((n : ℝ) - 1) := by linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
  have hdiv : (n.factorial : ℝ) / 2 ^ (n - 1) ≤ (n.factorial : ℝ) := by
    apply div_le_self hnfact.le
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hstep2 : Real.log ((n.factorial : ℝ) / 2 ^ (n - 1)) ≤ (n : ℝ) ^ 2 :=
    le_trans (Real.log_le_log hB hdiv) (log_factorial_le_sq n)
  rw [hcast]
  have hstep1 : ((n : ℝ) - 1) * Real.log (64 * n * d : ℝ) ≤ ((n : ℝ) - 1) * (64 * n * d : ℝ) :=
    mul_le_mul_of_nonneg_left hlogbase hn1_nonneg
  linarith [hstep1, hstep2]

end Work.BW
