import Mathlib
import Submission.Work.Analysis.Fourier.fejer_poly_eq_win
import Submission.Work.KMTAreas.A4.denseMultiples_defs

/-!
# The Fejér kernel packaging used by the "dense multiples" engine

`Work.Analysis.Fourier.fejerWin N x` is the normalised Fejér kernel of order `N+1`,
`(sin (π (N+1) x) / ((N+1) sin (π x)))²` (with value `1` at the integers).  Its trigonometric
expansion is `Work.Analysis.Fourier.fejer_poly_eq_win`.

For the Erdős–Turán discrepancy argument used in `denseMultiples_engine` it is convenient to use
the *classical* (mass-one) kernel `fejerKern N x = (N+1) * fejerWin N x`, whose full integral over
a period is `1` and whose mass on the window `[-1/(2(N+1)), 1/(2(N+1))]` is at least `3/4`.
-/

namespace Work.KMTAreas.A4

open scoped BigOperators

noncomputable section

/-- The normalised (mass `1`) Fejér kernel of order `N+1`. -/
def fejerKern (N : ℕ) (x : ℝ) : ℝ := ((N : ℝ) + 1) * Work.Analysis.Fourier.fejerWin N x

theorem fejerKern_nonneg (N : ℕ) (x : ℝ) : 0 ≤ fejerKern N x := by
  have h : 0 ≤ Work.Analysis.Fourier.fejerWin N x := by
    unfold Work.Analysis.Fourier.fejerWin
    split
    · norm_num
    · positivity
  have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  exact mul_nonneg hN h

theorem fejerKern_pos (N : ℕ) (x : ℝ) : 0 < ((N : ℝ) + 1) := by positivity

end

end Work.KMTAreas.A4
