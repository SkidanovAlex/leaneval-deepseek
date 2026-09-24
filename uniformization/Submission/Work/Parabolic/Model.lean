import ChallengeDeps
import Submission.Work.Parabolic.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# The model Green functions: the upper half plane

This module provides the *witness* used to prove that the hyperbolic end of the dichotomy is
incompatible with parabolicity: the Green function of the upper half plane `ℍ` with pole at `i`,

`greenUpperHalfPlane w = log (‖w + i‖ / ‖w - i‖)`,

together with the distinguished point `iUHP` (the pole).  It is the function `z ↦ log |(z+i)/(z-i)|`,
the classical Green function of the half plane with pole `i`: positive on `ℍ \ {i}`, harmonic off
`i`, and tending to `0` at the ideal boundary of `ℍ` (its superlevel sets are the closed
Apollonius discs around `i`, which are compact).

`Work.Parabolic.HasGreenFunctionAt (X := UpperHalfPlane) iUHP` — the statement that this is indeed
a Green function in the sense of `Basic.lean` — is proved in `UpperHalfPlaneGreen.lean`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.Parabolic

/-- The point `i` of the upper half plane: the pole of the model Green function. -/
def iUHP : UpperHalfPlane := ⟨Complex.I, by simp [Complex.I_im]⟩

/-- **The Green function of the upper half plane with pole at `i`**:
`w ↦ log (‖w + i‖ / ‖w - i‖) = log ‖(w+i)/(w-i)‖`. -/
def greenUpperHalfPlane (w : UpperHalfPlane) : ℝ :=
  Real.log (‖(w : ℂ) + Complex.I‖ / ‖(w : ℂ) - Complex.I‖)

/-- The same function, written on `ℂ` (for chart computations). -/
def greenUpperHalfPlaneC (z : ℂ) : ℝ :=
  Real.log (‖z + Complex.I‖ / ‖z - Complex.I‖)

theorem greenUpperHalfPlane_eq (w : UpperHalfPlane) :
    greenUpperHalfPlane w = greenUpperHalfPlaneC (w : ℂ) := rfl

theorem iUHP_coe : (iUHP : ℂ) = Complex.I := rfl

theorem iUHP_im : 0 < (iUHP : ℂ).im := by
  rw [iUHP_coe, Complex.I_im]; norm_num

theorem greenUpperHalfPlaneC_def (z : ℂ) :
    greenUpperHalfPlaneC z = Real.log (‖z + Complex.I‖ / ‖z - Complex.I‖) := rfl

@[simp]
theorem greenUpperHalfPlaneC_apply (z : ℂ) :
    greenUpperHalfPlaneC z = Real.log (‖z + Complex.I‖ / ‖z - Complex.I‖) := rfl

end Work.Parabolic
