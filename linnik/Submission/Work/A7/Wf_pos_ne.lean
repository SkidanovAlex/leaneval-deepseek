import Mathlib
import Submission.Work.LinnikAreas.A7.Defs

namespace Work.A7

/-- HB's density weight `Wf(λ) = w(λ) = λ/(e^{73λ/30} - e^{16λ/15})` is strictly positive for
every `λ ≠ 0`: writing `D(λ) = e^{73λ/30} - e^{16λ/15}`, the factors `λ` and `D(λ)` have the
same sign (`D(λ)` is negative exactly when `λ < 0`, since `x ↦ e^{73x/30} - e^{16x/15}` is
strictly increasing and vanishes at `0`). -/
theorem Wf_pos_ne {x : ℝ} (hx : x ≠ 0) : 0 < Work.LinnikAreas.A7.Wf x := by
  rw [Work.LinnikAreas.A7.Wf, Work.LinnikContract.wHB]
  rcases lt_or_gt_of_ne hx with h | h
  · exact div_pos_of_neg_of_neg h (by
      have : (73/30 : ℝ) * x < (16/15 : ℝ) * x := by nlinarith
      have := Real.exp_lt_exp.mpr this
      linarith)
  · exact div_pos h (by
      have : (16/15 : ℝ) * x < (73/30 : ℝ) * x := by nlinarith
      have := Real.exp_lt_exp.mpr this
      linarith)

end Work.A7
