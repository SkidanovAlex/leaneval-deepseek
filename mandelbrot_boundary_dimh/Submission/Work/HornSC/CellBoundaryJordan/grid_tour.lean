import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs

/-!
# The polygonal tour of a grid cycle

For a walk `u : ℕ → ℤ × ℤ` with unit steps, we build the polygonal parametrisation
`tourOn u k : ℝ → ℂ` of the closed curve

  `cycleSet k u = ⋃ i < k, adjSeg (u i) (u (i + 1))`,

traversing the `i`-th step affinely during the time interval `[i/k, (i+1)/k]`, together with its
`1`-periodic version `tour u k t = tourOn u k (Int.fract t)`.

This file contains the *definitions* only; the lemmas about them (continuity, the affine
description on each step, the range, and injectivity) live in the sibling files.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- The closed polygonal curve traced by the grid cycle `u`. -/
def cycleSet (k : ℕ) (u : ℕ → ℤ × ℤ) : Set ℂ :=
  ⋃ i ∈ {i : ℕ | i < k}, adjSeg (u i) (u (i + 1))

/-- The fraction of step `i` completed at step-time `s` (clipped to `[0,1]`). -/
def stepFrac (i : ℕ) (s : ℝ) : ℝ := max 0 (min (s - (i : ℝ)) 1)

/-- The polygonal walk starting at `lpt (u 0)` which traverses the `i`-th step during `[i, i+1]`. -/
noncomputable def tourOn (u : ℕ → ℤ × ℤ) (k : ℕ) (t : ℝ) : ℂ :=
  lpt (u 0) + ∑ i ∈ Finset.range k,
    (stepFrac i ((k : ℝ) * t)) • (lpt (u (i + 1)) - lpt (u i))

/-- The `1`-periodic polygonal tour. -/
noncomputable def tour (u : ℕ → ℤ × ℤ) (k : ℕ) (t : ℝ) : ℂ := tourOn u k (Int.fract t)

/-- The index of the step containing the "time" `t`. -/
noncomputable def edgeIdx (k : ℕ) (t : ℝ) : ℕ := ⌊(k : ℝ) * t⌋₊

/-- The `i`-th step vector of the walk. -/
def stepVec (u : ℕ → ℤ × ℤ) (i : ℕ) : ℂ := lpt (u (i + 1)) - lpt (u i)

lemma tour_def (u : ℕ → ℤ × ℤ) (k : ℕ) (t : ℝ) : tour u k t = tourOn u k (Int.fract t) := rfl

lemma stepVec_apply (u : ℕ → ℤ × ℤ) (i : ℕ) : stepVec u i = lpt (u (i + 1)) - lpt (u i) := rfl

end Work.HornSC.CellBoundaryJordan

namespace Work.HornSC.CellBoundaryJordan

/-- `HasArgPeriodic f` says that the closed curve `f` admits a continuous `1`-periodic argument
function, i.e. that its winding number around the origin is `0`.  This is
`Commons.Topology.Winding.HasArg f 0`. -/
def HasArgPeriodic (f : ℝ → ℂ) : Prop :=
  ∃ θ : ℝ → ℝ, Continuous θ ∧ (∀ t, θ (t + 1) = θ t) ∧
    ∀ t, f t = (‖f t‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)

end Work.HornSC.CellBoundaryJordan
