/-
# `Submission.Work.FIArea3.JointCount.maxPieceDefs` — the Finset of maximal piece generators

`GaussPieceMax d w` (from `pieces.lean`) says that `w` is a generator of a maximal piece of
`{z | d ∣ |z|²}`.  It is invariant under multiplication by a unit, and every such `w` has
`gnorm w ≤ d²`, hence `|Re w|, |Im w| ≤ d`.  To have one generator per maximal *piece* (ideal),
`maxPieceFinset d` keeps only the representative with `0 < Re w` and `0 ≤ Im w` — the standard
fundamental domain for the unit group `{±1, ±i}` of `ℤ[i]` acting by multiplication, in which
every nonzero Gaussian integer has exactly one associate.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.pieces

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The finite set of maximal piece generators of `{z : ℤ[i] | d ∣ |z|²}`, one per maximal
piece (ideal): the elements of `gBox d` that are `GaussPieceMax` and lie in the fundamental
domain `{0 < Re, 0 ≤ Im}` of the unit group. -/
def maxPieceFinset (d : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (d : ℤ)).filter (fun w => GaussPieceMax d w ∧ 0 < w.re ∧ 0 ≤ w.im)

end

end Work.FIArea3.JointCount
