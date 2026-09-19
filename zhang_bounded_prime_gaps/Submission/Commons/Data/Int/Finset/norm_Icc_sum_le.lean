import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Data.Finset.sum_Icc_eq_sum_log2_blocks

namespace Commons.Data.Int.Finset

open scoped BigOperators
set_option autoImplicit false

/-- Norm of the window sum over a consecutive integer window of length `N` with
unit-modulus coefficients is bounded by `N`. -/
theorem norm_Icc_sum_le {a : ℤ} {N : ℕ} (w : ℤ → ℂ) (hw : ∀ n : ℤ, ‖w n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Icc (a + 1) (a + (N : ℤ)), w n‖ ≤ (N : ℝ) := by
  calc
    ‖∑ n ∈ Finset.Icc (a + 1) (a + (N : ℤ)), w n‖
        ≤ ∑ n ∈ Finset.Icc (a + 1) (a + (N : ℤ)), ‖w n‖ := by
          simpa using (norm_sum_le (s := Finset.Icc (a + 1) (a + (N : ℤ))) (f := w))
    _ ≤ ∑ _n ∈ Finset.Icc (a + 1) (a + (N : ℤ)), (1 : ℝ) := by
          exact Finset.sum_le_sum (s := Finset.Icc (a + 1) (a + (N : ℤ)))
            (f := fun n => ‖w n‖) (g := fun _ => (1 : ℝ)) (by intro n _hn; exact hw n)
    _ = ((Finset.Icc (a + 1) (a + (N : ℤ))).card : ℝ) := by
          simp
    _ = (N : ℝ) := by
          rw [Int.card_Icc]
          norm_num

end Commons.Data.Int.Finset