import Mathlib

namespace Work.KMTAreas

/-- The series `∑_{n ≥ 0} 1 / (n + 1)^2` is summable and its sum is at most `2`.

This is the sharp enough bound `ζ 2 ≤ 2`; the proof uses the evaluation
`∑_{n ≥ 0} 1 / n^2 = π^2 / 6` (`hasSum_zeta_two`) together with the bound
`π < 3.15`, which gives `π^2 / 6 < 2`. -/
theorem tsum_one_div_sq_succ_le_two :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) ∧
      ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 2 := by
  -- `∑_{n ≥ 0} 1/(n+1)^2 = ∑_{n ≥ 0} 1/n^2 = π^2/6`, the shift being harmless
  -- because the `n = 0` term of the latter series vanishes.
  have hbase : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
      (Real.pi ^ 2 / 6 + ∑ i ∈ Finset.range 1, (1 : ℝ) / (i : ℝ) ^ 2) := by
    simpa using hasSum_zeta_two
  have hshift : HasSum (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2) (Real.pi ^ 2 / 6) :=
    (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).2 hbase
  have hsum : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    convert hshift using 2
    push_cast
    ring
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq]
  -- `π^2/6 ≤ 2` since `π^2 < 3.15^2 = 9.9225 < 12`
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

end Work.KMTAreas
