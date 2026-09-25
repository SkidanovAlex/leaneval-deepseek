/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The one-variable Cauchy-type transform used for the open polydisc `∂̄`-problem

This file collects the definitions used in the proof of
`Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc_open_aux`: the
unsupported `∂̄`-problem on a polydisc `P = polydisc c r` is solved by
processing the coordinates one at a time, using

  `dbarTransform ρ j g z = -(1/π) ∫_{‖w‖<ρ} g (z + w e_j) / w dw`

together with a smooth cutoff `openCut` in the transformed coordinate.

The concrete radii/constants are

* `cutIn  = 13/16`, `cutOut = 7/8`, `trRho = 7/4 = 2 * cutOut`,
* `trTrack = 15/16` (radius of the region where the intermediate data are tracked),
* `eqRad = 3/4` (radius of the polydisc on which the equation is solved).
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- Inner radius of the cutoff: `openCut = 1` for `‖ζ‖ ≤ cutIn`. -/
def cutIn : ℝ := 13 / 16

/-- Outer radius of the cutoff: `openCut = 0` for `cutOut ≤ ‖ζ‖`. -/
def cutOut : ℝ := 7 / 8

/-- Radius of the disc over which the Cauchy-type transform is integrated. -/
def trRho : ℝ := 7 / 4

/-- Radius of the region on which the intermediate data are tracked. -/
def trTrack : ℝ := 15 / 16

/-- Radius of the polydisc on which the `∂̄`-equation is solved. -/
def eqRad : ℝ := 3 / 4

/-- A smooth cutoff on `ℂ`, equal to `1` on `‖ζ‖ ≤ cutIn` and to `0` for `cutOut ≤ ‖ζ‖`. -/
def openCut (ζ : ℂ) : ℂ :=
  (Real.smoothTransition ((cutOut ^ 2 - ‖ζ‖ ^ 2) / (cutOut ^ 2 - cutIn ^ 2)) : ℂ)

/-- The Cauchy-type transform in the `j`-th coordinate, integrated over the disc of
radius `ρ`: `dbarTransform ρ j g z = -(1/π) ∫_{‖w‖<ρ} g (z + w e_j)/w dw`. -/
def dbarTransform {n : ℕ} (ρ : ℝ) (j : Fin n) (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  -((Real.pi : ℂ))⁻¹ *
    ∫ w in Metric.ball (0 : ℂ) ρ, g (z + Function.update (0 : Fin n → ℂ) j w) / w

/-- The region on which the data at stage `j` are tracked: all coordinates below `trTrack`. -/
def trackSet {n : ℕ} : Set (Fin n → ℂ) := {z | ∀ l, ‖z l‖ < trTrack}

@[simp] lemma mem_trackSet {n : ℕ} {z : Fin n → ℂ} :
    z ∈ trackSet ↔ ∀ l, ‖z l‖ < trTrack := Iff.rfl

/-- The region on which the `∂̄`-equation is solved: all coordinates below `eqRad`. -/
def solveSet {n : ℕ} : Set (Fin n → ℂ) := {z | ∀ l, ‖z l‖ < eqRad}

@[simp] lemma mem_solveSet {n : ℕ} {z : Fin n → ℂ} :
    z ∈ solveSet ↔ ∀ l, ‖z l‖ < eqRad := Iff.rfl

end Work.CR.Flat.Cauchy
