import Mathlib
import Submission.Work.Pert.Basic

namespace Work.Pert

theorem walk_defect_sum {R : ℂ → ℂ} {α : ℂ} {w : ℂ} {m : ℕ} {A : ℝ}
    (h : ∀ j : ℕ, j < m → ‖R (R^[j] w) - R^[j] w + 1 / α‖ ≤ A) :
    ‖(m : ℂ) / α + (R^[m] w - w)‖ ≤ (m : ℝ) * A := by
  -- Rewrite the left-hand side as the sum of the individual defects along the walk.
  have hkey : (m : ℂ) / α + (R^[m] w - w)
      = ∑ j ∈ Finset.range m, (R (R^[j] w) - R^[j] w + 1 / α) := by
    have htel : (∑ j ∈ Finset.range m, (R (R^[j] w) - R^[j] w)) = R^[m] w - w := by
      have := Finset.sum_range_sub (fun j => R^[j] w) m
      simpa [Function.iterate_succ_apply'] using this
    rw [Finset.sum_add_distrib, htel]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hkey]
  calc ‖∑ j ∈ Finset.range m, (R (R^[j] w) - R^[j] w + 1 / α)‖
      ≤ ∑ j ∈ Finset.range m, ‖R (R^[j] w) - R^[j] w + 1 / α‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range m, A :=
        Finset.sum_le_sum (fun j hj => h j (Finset.mem_range.mp hj))
    _ = (m : ℝ) * A := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Work.Pert
