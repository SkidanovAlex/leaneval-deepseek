import Mathlib
import Submission.Work.Drive.WindingNumber

/-!
# The square and its boundary loop (vocabulary for the `mod 2` degree theorem)

The `mod 2` degree theorem for a map of the square relates the number of zeros of `F` in the square
`[0,1]²` to the winding number of the boundary loop `F|∂□` about the origin.  This file collects the
elementary vocabulary of that statement: the square, its boundary, and the boundary loop (a
parametrization of `∂[0,1]²` of period `4`, read on `ℝ/ℤ`).
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- The closed unit square `[0,1]²` in `ℝ²`. -/
def sqBox : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1}

/-- The boundary of the unit square: a point of the square with one coordinate `0` or `1`. -/
def sqBoxBdry : Set (ℝ × ℝ) :=
  {p | p ∈ sqBox ∧ (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1)}

/-- The counterclockwise parametrization of the boundary of `[0,1]²`, of period `4`, starting at
`(0,0)`: the four edges are traversed at unit speed. -/
def sqBoxLoop (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 then (t, 0)
  else if t ≤ 2 then (1, t - 1)
  else if t ≤ 3 then (3 - t, 1)
  else (0, 4 - t)

/-- **The boundary loop of the square, read on `ℝ/ℤ`.**  The loop `sqBoxLoop` has period `4`, so
`t ↦ F (sqBoxLoop (4 t))` is a curve of period `1`; it is the boundary curve of `F`. -/
def sqBoxBdyCurve (F : ℝ × ℝ → ℝ × ℝ) : UnitAddCircle → ℝ × ℝ :=
  AddCircle.liftIco 1 0 fun t : ℝ => F (sqBoxLoop (4 * t))

end

end Work.Drive
