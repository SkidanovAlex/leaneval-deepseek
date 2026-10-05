import Mathlib
import Submission.Work.RPB.B1.AreaPosDefs

/-!
# Vocabulary for `Work.RPB.B1.windInt_lift`

The integral form of the winding number `windInt u q = (1/2π) ∮ Im (u'/(u-q))` is the
primitive `s ↦ ∫_0^s Im (u'/u)` of the winding integrand, divided by `2π`.  This file names the
two objects the proof of `windInt_lift` works with:

* `windPhase u s = ∫_0^s Im (u'/u)` — the *unwound* angle along the curve, defined without any
  lifting theory as an integral;
* `windDir u s = e^{-i·windPhase u s} · u s` — the curve rotated by the negative of that angle.
  Its defining property (proved in `Submission.Work.RPB.B1.WindDirDeriv`) is that its derivative is a
  real (in fact `Re (u'/u)`) multiple of itself, so that its *direction* is constant; that is the
  content of the classical identity `e^{i·windPhase u s}·(u s/‖u s‖) = u 0/‖u 0‖`, from which both
  halves of `windInt_lift` follow.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1

/-- The primitive of the winding integrand: `windPhase u s = ∫_0^s Im (u'(x)/u(x)) dx`. -/
def windPhase (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..s, (deriv u x / u x).im

/-- The curve `u` rotated by the negative of the unwound angle `windPhase u`:
`windDir u s = e^{-i·windPhase u s} · u s`. -/
def windDir (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  Complex.exp (-((windPhase u s : ℂ) * Complex.I)) * u s

@[simp] lemma windPhase_zero (u : ℝ → ℂ) : windPhase u 0 = 0 := by
  simp [windPhase]

@[simp] lemma windDir_zero (u : ℝ → ℂ) : windDir u 0 = u 0 := by
  simp [windDir]

end Work.RPB.B1
