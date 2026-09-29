import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.pbCostArithKit
import Submission.Work.Resample.pbRndDefs

namespace Work.Resample

/-- The `prep`-table terms of the per-axis budgets, summed over the `D` axes:
`Σ_{j<D} (t_j + 1) ≤ 2 * ts.sum` (each `t_j ≥ 2`, so `ts.sum ≥ D`). -/
theorem paDSumT {p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts) :
    (∑ j ∈ Finset.range HvdH.D, (ts.getD j 0 + 1)) ≤ 2 * ts.sum := by
  -- each axis has `t j ≥ 3`, hence `3 * D ≤ ts.sum`
  have hsum3 : 3 * HvdH.D ≤ ts.sum := pbRnd_sum3D p α ss ts h
  obtain ⟨_, htslen, -⟩ := h
  -- the sum splits into `ts.sum` plus `D` ones
  have hsplit : (∑ j ∈ Finset.range HvdH.D, (ts.getD j 0 + 1)) = ts.sum + HvdH.D := by
    rw [Finset.sum_add_distrib, pbRnd_sum_range_getD ts HvdH.D htslen]
    simp
  omega

end Work.Resample
