import Mathlib
import Submission.Work.Drive.chordSweepSmooth

/-!
# The generalised chamfer loop of the lead's uniform-`ρ₀` design (`NOTES_LEAD_endgameUniform.md` §3)

`Work.Drive.chamferLoopGen r D lay α β` is the chord-sweep loop with

* a *fixed layout* `lay` (the width of the two chamfer junctions in the loop parameter, the same for
  every slice — this is what keeps the junction positions σ-independent, which the σ-blur's
  half-space margins need),
* a **σ-scheduled** arc-depth fraction `α` (the retained arc is `[α σ, 1 - α σ]` of the slice), and
* a **σ-scheduled** chord-target fraction `β` (the connectors join the cut arc points to the chord
  points at fractions `β σ` and `1 - β σ`).

With `α = β = λ` constant it is `Work.Drive.sweepLoopChamfer r D λ` (`chamferLoopGen_const`), so the
whole existing chamfer machinery (the needle end, the wide-end estimate, the blur) applies verbatim
on the part of the window where the schedule is constant.

The point of the generalisation is the lead's uniform `ρ₀`: the *depth* `α σ * sweepW' D σ` is an
absolute length (so the fatness scale `ρ` enters through a uniform constant instead of through
`ρ ≤ lam * W` with a crosscut-dependent `lam`), while `lay` stays a *post-crosscut* layout
parameter.  `Lemma A` (`Work.Drive.chamferLoopGen_injOn_ball`, delegated) proves the injectivity of
the slices in the zones where the depth is absolute; `Lemma B`
(`Work.Drive.chamferLoopGen_injOn_nt`, the per-σ refactor of `Work.Drive.chamferLoop_injOn_nt`)
covers the zones where the depth is the standard `lay * W`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The generalised chamfer loop** (lead's `NOTES_LEAD_endgameUniform.md` §3), verbatim. -/
def chamferLoopGen (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lay : ℝ) (α β : ℝ → ℝ)
    (s t : ℝ) : Space :=
  let u := sweepParam t
  if u ≤ 1 / 2 then sweepArc' r D s (α s + (1 - 2 * α s) * (2 * u))
  else if u ≤ 1 / 2 + lay / 2 then
    (1 - (2 * u - 1) / lay) • sweepArc' r D s (1 - α s)
      + ((2 * u - 1) / lay) • sweepChord' r D s (1 - β s)
  else if u ≤ 1 - lay / 2 then
    sweepChord' r D s ((1 - β s) - ((u - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β s))
  else (1 - (u - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D s (β s)
      + ((u - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D s (α s)

/-- The constant schedule gives back the ordinary chamfered sweep loop. -/
lemma chamferLoopGen_const (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam : ℝ) :
    chamferLoopGen r D lam (fun _ => lam) (fun _ => lam) = sweepLoopChamfer r D lam := by
  funext s t
  simp only [chamferLoopGen, sweepLoopChamfer]

end Work.Drive
