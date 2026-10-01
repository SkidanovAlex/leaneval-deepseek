import Mathlib

namespace Work.LinnikAreas.Density4

/-- Telescoping identity for the `1/sqrt (n-1) - 1/sqrt n` summands appearing in
Linnik's theorem: the finite sum over `Icc 2 M` collapses to `1 - 1/sqrt M`. -/
theorem sqrt_delta_telescope (M : ℕ) (hM : 2 ≤ M) :
    (∑ n ∈ Finset.Icc 2 M, (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)))
      = 1 - 1 / Real.sqrt (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
    rw [ih]
    have hcast : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
    rw [hcast]
    ring

end Work.LinnikAreas.Density4
