import Mathlib
import Submission.Work.Drive.strip_defs

/-!
# The strip of chord parameters and its covering map to the band of secants

This module fixes the vocabulary of the *strip cover* used by
`Work.Drive.isPathConnected_component_liftedTrisecant`:

* `Work.Drive.StripPeriod` — the open strip `{0 < y < period}` of chord parameters
  `(x, y) = (starting parameter, chord parameter length)`, as a type;
* `Work.Drive.stripClass p` — the covering map `p ↦ {K x, K (x + y)}` from the strip to
  Kuperberg's open Möbius band `OpenMobius` of secant classes
  (`stripSecantClass p.1 p.2.1 p.2.2`), packaged as a plain function of the strip point so
  that lemmas about it (openness, local injectivity, local path connectedness) can be stated
  without carrying the distinctness witnesses.

The two substitutions of the cover are
`(x,y) ↦ (x + y, period − y)` (`stripFlip`, the deck generator) and `(x,y) ↦ (x + period, y)`
(the square of the deck generator).
-/

open LeanEval.KnotTheory.Quadrisecant

namespace Work.Drive

/-- The strip `{q : ℝ × ℝ | 0 < q.2 ∧ q.2 < period}` of chord parameters, as a type. -/
abbrev StripPeriod : Type := {q : ℝ × ℝ // 0 < q.2 ∧ q.2 < period}

/-- **The covering map of the strip onto the band of secants**: the secant class
`{K x, K (x + y)}` of the chord of parameter length `y` starting at `x`. -/
noncomputable def stripClass (p : StripPeriod) : OpenMobius :=
  stripSecantClass p.1 p.2.1 p.2.2

@[simp] lemma stripClass_val (p : StripPeriod) :
    stripClass p = stripSecantClass p.1 p.2.1 p.2.2 := rfl

/-- The strip point underlying a point of the lifted trisecant locus. -/
noncomputable def toStrip {r : ℝ → Space} (p : ↥(liftedTrisecant r)) : StripPeriod :=
  ⟨p.1, (mem_liftedTrisecant_iff.mp p.2).choose,
    (mem_liftedTrisecant_iff.mp p.2).choose_spec.choose⟩

@[simp] lemma toStrip_val {r : ℝ → Space} (p : ↥(liftedTrisecant r)) :
    (toStrip p : ℝ × ℝ) = p.1 := rfl

lemma stripClass_toStrip_mem {r : ℝ → Space} (p : ↥(liftedTrisecant r)) :
    stripClass (toStrip p) ∈ trisecantSet r :=
  (mem_liftedTrisecant_iff.mp p.2).choose_spec.choose_spec

end Work.Drive
