import Mathlib
import Submission.Work.Milnor.QuatSphere
import Submission.Work.Milnor.Construction
import Submission.Work.Milnor.MorseFun

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for `Work.Milnor.morseChart_crit`

The chart expressions `morseChart1`, `morseChart2` of the Morse function on `Mk (-2)` are
products of a function of the base coordinate (the sphere coordinate) and a function of the
fibre coordinate.  This file collects the pieces and some elementary facts about them.
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace
open TopologicalSpace Set Metric
open Submission.Milnor

namespace Work.Milnor

noncomputable section

/-- The model space of `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- The model space of `S³`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The model space of `MSpace = ℝ⁴ × S³`. -/
abbrev ME : Type := E4 × E3

/-- `η u = 1/√(1+‖u‖²)`, the factor of `morseChart2` depending on the base coordinate. -/
def eta (u : E4) : ℝ := (Real.sqrt (1 + ‖u‖ ^ 2))⁻¹

/-- `h v = (4-‖v‖²)/(4+‖v‖²)`. -/
def hfun (v : E3) : ℝ := (4 - ‖v‖ ^ 2) / (4 + ‖v‖ ^ 2)

/-- The factor `1/√(1+‖p.1‖²)` of `morseChart2` on `MSpace`. -/
def Hfun (p : MSpace) : ℝ := eta p.1

/-- The factor `Re(p.2)` of `morseChart2` on `MSpace`. -/
def Gfun (p : MSpace) : ℝ := (p.2 : Quaternion ℝ).re

/-- The factor `Re(ẋ * p.2)` of `morseChart1` on `MSpace`, with `ẋ = Quaternion.linearIsometryEquivTuple.symm p.1`. -/
def Gfun1 (p : MSpace) : ℝ :=
  (Quaternion.linearIsometryEquivTuple.symm p.1 * (p.2 : Quaternion ℝ)).re

/-- The scalar factor in `fderiv eta`. -/
def ceta (u : E4) : ℝ := - (1 + ‖u‖ ^ 2) ^ (-(3/2 : ℝ))

/-- The scalar factor in `fderiv hfun`. -/
def cgam (u : E3) : ℝ := - 16 * (4 + ‖u‖ ^ 2) ^ (-(2 : ℝ))

lemma morseChart2_eq (p : MSpace) : morseChart2 p = Gfun p * Hfun p := by
  rw [morseChart2, Gfun, Hfun, eta, div_eq_mul_inv]

lemma morseChart1_eq (p : MSpace) : morseChart1 p = Gfun1 p * Hfun p := by
  rw [morseChart1, Gfun1, Hfun, eta, div_eq_mul_inv]

end
end Work.Milnor
