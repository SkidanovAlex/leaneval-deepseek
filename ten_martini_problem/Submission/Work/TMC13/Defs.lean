import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.RotBasics.Defs

/-!
# TMC13 — vocabulary for the conjugating lift

Shared definitions for `Work.TMC13.conjugating_lift`.

For a real `2×2` matrix `A` and `t : ℝ`, `smul A (vc t) ∈ ℂ` is the image of the unit
vector `vc t = (cos πt, sin πt)`.  It is a Fourier polynomial of degree one in `t`:

  `smul A (vc t) = c1 A * vc t + c2 A * conj (vc t)`,

with the amplitude coefficients `c1 A, c2 A` defined below.  The key identity is
`‖c1 A‖² − ‖c2 A‖² = det A`, so for `det A = 1` the leading coefficient dominates and
`smul A (vc t) ≠ 0` for all `t`.
-/

namespace Work.TMC13

noncomputable section

/-- Leading Fourier coefficient of `t ↦ smul A (vc t)`. -/
def c1 (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (((A 0 0 + A 1 1) / 2 : ℝ) : ℂ) + (((A 1 0 - A 0 1) / 2 : ℝ) : ℂ) * Complex.I

/-- Conjugate Fourier coefficient of `t ↦ smul A (vc t)`. -/
def c2 (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (((A 0 0 - A 1 1) / 2 : ℝ) : ℂ) + (((A 0 1 + A 1 0) / 2 : ℝ) : ℂ) * Complex.I

end

end Work.TMC13
