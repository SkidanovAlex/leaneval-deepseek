import Mathlib
import Submission.Work.TMContract.Defs

namespace Work.TMComp.Kotani

open Work.TMContract

/-- The single transfer matrix `tmC lam E y = !![E - v(y), -1; 1, 0]` has determinant `1`. -/
theorem det_tmC (lam : ℝ) (E : ℂ) (y : ℝ) : (tmC lam E y).det = 1 := by
  simp [tmC, Matrix.det_fin_two]

/-- Every iterate `iterC α lam E n x = S(x+(n-1)α) ⋯ S(x)` is a product of determinant-one
matrices, hence has determinant `1`. -/
theorem det_iterC (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    (Work.TMContract.iterC α lam E n x).det = 1 := by
  induction n with
  | zero => simp only [iterC, Matrix.det_one]
  | succ n ih =>
      rw [iterC, Matrix.det_mul, ih, det_tmC, mul_one]

end Work.TMComp.Kotani
