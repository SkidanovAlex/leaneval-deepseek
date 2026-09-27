import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.Defs

/-!
# The conjugate Cauchy--Riemann operator `dbarBar`

The companion `∂_x - i ∂_y` of the workspace's `dbar = ∂_x + i ∂_y` (which is `2 ∂_z̄`); `dbarBar`
is `2 ∂_z`.  It is the operator whose *formal adjoint* with respect to the weighted measure
`e^{-φ} dz` controls the weighted `L²` theory of `∂̄` (the Hörmander basic estimate): the adjoint of
`dbar` is `u ↦ u · dbarBar φ - dbarBar u`, and the Bochner--Kodaira identity in one variable reads

  `∫ ‖dbarBar u - u · dbarBar φ‖² e^{-φ} = ∫ ‖dbar u‖² e^{-φ} + ∫ Δφ ‖u‖² e^{-φ}`,

whose right-hand side is `≥ c ∫ ‖u‖² e^{-φ}` when `Δφ ≥ c`.  Note `dbar (dbarBar φ) = Δφ` for
real-valued `φ`.
-/

open MeasureTheory

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- **The conjugate Cauchy--Riemann operator** `∂_x - i ∂_y = 2 ∂_z`, written with the real Fréchet
derivative. -/
def dbarBar (f : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I

@[simp]
theorem dbarBar_const (c : ℂ) (z : ℂ) : dbarBar (fun _ : ℂ => c) z = 0 := by
  simp [dbarBar]

end Work.Analysis.Complex.DbarCauchy
