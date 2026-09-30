import Mathlib
import Submission.Work.BMF.card_primeFactors_filter_le_mul_log

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For `q ≥ 1` and `1 ≤ N ≤ x + 2`, the number of distinct prime factors of `q` times `log N`
is at most `(2/log 2) · log(q+2) · log(x+2)`: combine `ω(q)·log 2 ≤ log q ≤ log(q+2)` with
`log N ≤ log(x+2)`. -/
theorem v7_log_omega_bound (q N : ℕ) (x : ℝ) [NeZero q] (hN : 1 ≤ N) (hNx : (N : ℝ) ≤ x + 2) :
    (2 : ℝ) * ((q.primeFactors.card : ℝ) * Real.log N)
      ≤ (2 / Real.log 2) * Real.log ((q : ℝ) + 2) * Real.log (x + 2) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `ω(q) · log 2 ≤ log q ≤ log (q+2)`.
  have h1 : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log ((q : ℝ) + 2) := by
    have hbase := Work.BMF.card_primeFactors_filter_le_mul_log q 2 hq1 (by norm_num)
    have hfil : q.primeFactors.filter (fun p => 2 ≤ p) = q.primeFactors :=
      Finset.filter_true_of_mem
        (fun p hp => Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
    rw [hfil] at hbase
    have hbase' : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (q : ℝ) := by
      simpa using hbase
    have hlog : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) + 2) :=
      Real.log_le_log (by exact_mod_cast hq1) (by linarith [show (1 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq1])
    linarith
  have hLN_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hLq_nonneg : 0 ≤ Real.log ((q : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hLN_le : Real.log (N : ℝ) ≤ Real.log (x + 2) := Real.log_le_log (by linarith) hNx
  -- Multiply out: `2 · ω(q) · log N · log 2 ≤ 2 · log(q+2) · log(x+2)`.
  have main : (2 : ℝ) * ((q.primeFactors.card : ℝ) * Real.log N) * Real.log 2
      ≤ 2 * Real.log ((q : ℝ) + 2) * Real.log (x + 2) := by
    have e1 : (2 : ℝ) * ((q.primeFactors.card : ℝ) * Real.log N) * Real.log 2
        = ((q.primeFactors.card : ℝ) * Real.log 2) * (2 * Real.log N) := by ring
    rw [e1]
    calc ((q.primeFactors.card : ℝ) * Real.log 2) * (2 * Real.log (N : ℝ))
        ≤ Real.log ((q : ℝ) + 2) * (2 * Real.log N) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ Real.log ((q : ℝ) + 2) * (2 * Real.log (x + 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hLq_nonneg
      _ = 2 * Real.log ((q : ℝ) + 2) * Real.log (x + 2) := by ring
  -- Divide by `log 2 > 0`.
  have hfinal : (2 : ℝ) * ((q.primeFactors.card : ℝ) * Real.log N)
      ≤ (2 * Real.log ((q : ℝ) + 2) * Real.log (x + 2)) / Real.log 2 :=
    (le_div_iff₀ hL2pos).mpr main
  have heq : (2 * Real.log ((q : ℝ) + 2) * Real.log (x + 2)) / Real.log 2
      = (2 / Real.log 2) * Real.log ((q : ℝ) + 2) * Real.log (x + 2) := by
    field_simp
  rwa [heq] at hfinal

end Work.BMF
