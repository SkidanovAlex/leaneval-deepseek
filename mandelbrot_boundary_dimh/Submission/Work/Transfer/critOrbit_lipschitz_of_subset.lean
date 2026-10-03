import Mathlib
import Submission.Work.Transfer.Setup

namespace Work.Transfer

/-- Uniform-in-`j` Lipschitz bound for the critical orbit on a ball contained in `Mandelbrot`.

Inside `Mandelbrot` the critical orbit is bounded by `2`, so Cauchy's estimate gives a
Lipschitz constant `2 * 2 / ε` for every `critOrbit j` on the half-ball `ball c (ε/2)`. -/
theorem critOrbit_lipschitz_of_subset (hM : MandelDim.MsetStatement) {c : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hsub : Metric.ball c ε ⊆ LeanEval.Dynamics.MandelbrotBoundary.Mandelbrot) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ j : ℕ, ∀ z ∈ Metric.ball c (ε / 2), ∀ w ∈ Metric.ball c (ε / 2),
      ‖Work.Transfer.critOrbit j z - Work.Transfer.critOrbit j w‖ ≤ κ * ‖z - w‖ := by
  refine ⟨2 * 2 / ε, by positivity, fun j => ?_⟩
  refine lipschitz_of_norm_le_ball (f := critOrbit j) (R := ε) (M := 2) hε (by norm_num)
    (differentiableOn_critOrbit j _) ?_
  intro z hz
  rw [critOrbit_eq_iterate_zero]
  exact hM.2.2.1 z (hsub hz) (j + 1)

end Work.Transfer
