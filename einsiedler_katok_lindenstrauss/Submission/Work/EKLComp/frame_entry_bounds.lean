import Mathlib
import Submission.Work.EKLComp.FrameDefs

namespace Work.EKLComp

theorem frame_entry_bounds (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    ∀ i j, |(Work.EKLComp.Mmat v) i j| ≤ 1 := by
  -- The entries of `Mmat v = MB v * MA v` are either a single coefficient among
  -- `ca, cb, cc, cd` (each of absolute value at most one, by `FrameDefs`), or a product of two
  -- of them.  The product bound is immediate from `|a|, |b| ≤ 1`.
  have hca := abs_ca_le_one v
  have hcb := abs_cb_le_one v
  have hcc := abs_cc_le_one v hv
  have hcd := abs_cd_le_one v hv
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Mmat, MB, MA, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (first
      | exact hca | exact hcb | exact hcc | exact hcd
      | nlinarith [abs_nonneg (ca v), abs_nonneg (cb v),
          abs_nonneg (cc v), abs_nonneg (cd v)])

end Work.EKLComp
