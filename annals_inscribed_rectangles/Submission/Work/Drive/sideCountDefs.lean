import Mathlib
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.CappingSpace
import Submission.Work.Drive.BoxParityDefs

/-!
# `sideCount`: the parity input of the side value (lead's design, 2026-09-25 04:20)

The lead's genericity design for the chain route replaces the (false) equation
`sideOf = 1 ↔ the cut is non-empty` by a **loop-vs-sweep count**: for a chart `Q : ℂ → CappingSpace`,
a level `c` and a plane presentation `P`,

> `sideCount Q c P = #{q ∈ [0,1] × unitBox 2 | the core loop of the plane through `Q` meets the sweep
>   `clampedSweep c (1 - ·) P` at `q.2`}`,

where the loop is `t ↦ Q (exp (i π t))` (this is a *closed* loop because the chart satisfies the seam
clause `Q (-z) = Q z`, so `Q (exp 0) = Q (-1) = Q 1`) and the sweep is the 3-chain of the rotated
plane.  The loop has 1 parameter, the sweep has 3 (`Amb 2 = ℝ³`), and the ambient is the 4-manifold
`CappingSpace`, so the solutions are generically *isolated*; `SideRegular` says they are interior in
the box and that the two tangent images span the tangent space.

The side value of the chain route is `e u := Odd (sideCount (linCapping A ∘ Q) c (linCapping A' ∘
rotPresentation Q u))` for small `SideRegular` perturbations `(A, A')`; `Odd` is well defined,
rotation invariant and continuous in `u` by the parity theorem `odd_sideCount_iff_of_family` (to be
proved on top of this file, using `generic_regularization_gen` and
`Work.Drive.locallyConstant_labelMeet_eq`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-- The core loop of the plane presentation `Q`, read through the chart. -/
def coreLoop (Q : ℂ → CappingSpace) (t : ℝ) : CappingSpace :=
  Q (Complex.exp (Real.pi * (t : ℂ) * Complex.I))

/-- The set of parameters at which the core loop of `Q` meets the clamped sweep of `P` at level `c`
with the clamp `t ↦ 1 - t`. -/
def coreMeet (Q : ℂ → CappingSpace) (c : ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    Set (ℝ × Work.Drive.Amb 2) :=
  {q | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Submission.Drive.unitBox 2 ∧
    coreLoop Q q.1 = clampedSweep c (fun t => 1 - t) P q.2}

/-- **The loop-vs-sweep count** whose parity is the side value of the chain route. -/
def coreSideCount (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) : ℕ :=
  (coreMeet Q c P).ncard

end

end Work.Drive
