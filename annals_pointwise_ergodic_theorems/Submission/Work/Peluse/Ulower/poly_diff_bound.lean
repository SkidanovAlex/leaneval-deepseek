import Mathlib
import Submission.Work.Peluse.Ulower.ss_aux_poly_diff

namespace Work.Peluse.Ulower

/-- For `y, y' ≤ N` the difference `|P y - P y'|` is at most `C N^{deg P - 1} |y - y'|`. -/
theorem poly_diff_bound (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N y y' : ℕ), 1 ≤ N → y ≤ N → y' ≤ N →
      |((P.eval (y : ℤ) : ℤ) : ℝ) - ((P.eval (y' : ℤ) : ℤ) : ℝ)|
        ≤ C * (N : ℝ) ^ (P.natDegree - 1) * |(y : ℝ) - (y' : ℝ)| := ss_aux_poly_diff P hP

end Work.Peluse.Ulower
