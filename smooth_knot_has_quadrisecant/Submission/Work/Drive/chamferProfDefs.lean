import Mathlib
import Submission.Work.Drive.chamferLoopGenDefs

/-!
# The profile of the generalised chamfer loop

`Work.Drive.chamferLoopGen r D lay α β s t` is written in terms of the profile
`u = sweepParam t ∈ [0,1)` (see `Work.Drive.chamferLoopGen`).  This module removes the last
`period`-bookkeeping from the *geometric* analysis of the loop: `Work.Drive.chamferProfGen` is the
same piecewise formula with the profile `u` as the variable and the two cut fractions `a = α s`,
`b = β s` as parameters.

The loop runs, on `[0,1]`:

* `u ∈ [0, 1/2]`            : the retained *arc*, from fraction `a` to fraction `1 - a`;
* `u ∈ [1/2, 1/2+lay/2]`    : the head connector, the segment from `sweepArc' (1-a)` to
  `sweepChord' (1-b)`;
* `u ∈ [1/2+lay/2, 1-lay/2]`: the *chord*, from fraction `1 - b` back to fraction `b`;
* `u ∈ [1-lay/2, 1]`        : the tail connector, the segment from `sweepChord' b` to
  `sweepArc' a`.

`Work.Drive.chamferLoopGen_eq_prof` identifies the loop with the profile at `sweepParam t`, so that
injectivity of the profile on `[0,1)` gives injectivity of the loop on `[0, period)`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The profile of the generalised chamfer loop**: the same piecewise formula as
`Work.Drive.chamferLoopGen`, with the profile `u` in place of `sweepParam t` and the cut fractions
`a` (arc) and `b` (chord) as explicit parameters. -/
def chamferProfGen (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lay a b s u : ℝ) : Space :=
  if u ≤ 1 / 2 then sweepArc' r D s (a + (1 - 2 * a) * (2 * u))
  else if u ≤ 1 / 2 + lay / 2 then
    (1 - (2 * u - 1) / lay) • sweepArc' r D s (1 - a)
      + ((2 * u - 1) / lay) • sweepChord' r D s (1 - b)
  else if u ≤ 1 - lay / 2 then
    sweepChord' r D s ((1 - b) - ((u - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b))
  else (1 - (u - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D s b
      + ((u - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D s a

/-- **The loop is the profile at the loop parameter.** -/
lemma chamferLoopGen_eq_prof (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lay : ℝ)
    (α β : ℝ → ℝ) (s t : ℝ) :
    chamferLoopGen r D lay α β s t = chamferProfGen r D lay (α s) (β s) s (sweepParam t) := rfl

/-! ## The four branch formulas -/

/-- Branch 1 (`u ≤ 1/2`): the arc point at fraction `a + (1-2a)·2u`. -/
lemma chamferProfGen_arc {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay a b s u : ℝ}
    (h : u ≤ 1 / 2) :
    chamferProfGen r D lay a b s u = sweepArc' r D s (a + (1 - 2 * a) * (2 * u)) := by
  rw [chamferProfGen, if_pos h]

/-- Branch 2 (`u > 1/2`, `u ≤ 1/2 + lay/2`): the head connector from `sweepArc' (1-a)` to
`sweepChord' (1-b)`. -/
lemma chamferProfGen_head {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lay a b s u : ℝ}
    (h1 : ¬ u ≤ 1 / 2) (h2 : u ≤ 1 / 2 + lay / 2) :
    chamferProfGen r D lay a b s u
      = (1 - (2 * u - 1) / lay) • sweepArc' r D s (1 - a)
        + ((2 * u - 1) / lay) • sweepChord' r D s (1 - b) := by
  rw [chamferProfGen, if_neg h1, if_pos h2]

/-- Branch 3 (`u > 1/2 + lay/2`, `u ≤ 1 - lay/2`): the chord point at fraction
`(1-b) - ((u - (1/2+lay/2))/(1/2-lay))·(1-2b)`. -/
lemma chamferProfGen_chord {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay a b s u : ℝ} (h1 : ¬ u ≤ 1 / 2) (h2 : ¬ u ≤ 1 / 2 + lay / 2) (h3 : u ≤ 1 - lay / 2) :
    chamferProfGen r D lay a b s u
      = sweepChord' r D s ((1 - b) - ((u - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b)) := by
  rw [chamferProfGen, if_neg h1, if_neg h2, if_pos h3]

/-- Branch 4 (`u > 1/2`, `u > 1/2 + lay/2`, `u > 1 - lay/2`): the tail connector from
`sweepChord' b` to `sweepArc' a`. -/
lemma chamferProfGen_tail {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay a b s u : ℝ} (h1 : ¬ u ≤ 1 / 2) (h2 : ¬ u ≤ 1 / 2 + lay / 2) (h3 : ¬ u ≤ 1 - lay / 2) :
    chamferProfGen r D lay a b s u
      = (1 - (u - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D s b
        + ((u - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D s a := by
  rw [chamferProfGen, if_neg h1, if_neg h2, if_neg h3]

end Work.Drive
