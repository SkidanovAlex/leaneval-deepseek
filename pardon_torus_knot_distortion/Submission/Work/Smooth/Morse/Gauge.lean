import Mathlib
import Submission.Box

/-!
# An explicit rounded-box gauge for Pardon's boxes

The sweep theorems of this chapter (`Work.Smooth.Morse.boxSweep_containsEssentialLoop_of_crossing_on`
and its variants) take the *sandwich*

`PBox(t) ⊆ {g < t} ⊆ PBox((1+δ) t)`

for a function `g` as a hypothesis.  This file provides an explicit, elementary candidate: the
`ℓ^{2k}`-gauge

`boxGauge c σ k y = (Σ_i |(y (σ i) - c (σ i)) / boxSide i|^{2k})^{1/(2k)}`

with respect to Pardon's box `Submission.PBox` (`Submission.Box`).  It satisfies

* `Work.Smooth.Morse.Gauge.PBox_subset_boxGauge`:
  `PBox(t) ⊆ {boxGauge < (3 : ℝ)^{1/(2k)} · t}`,
* `Work.Smooth.Morse.Gauge.boxGauge_subset_PBox`:
  `{boxGauge < t} ⊆ PBox(t)`,

i.e. the sandwich with room `δ = 3^{1/(2k)} - 1`, which tends to `0` as `k → ∞` (for `k = 28` it is
below `2%`, the room of Pardon's argument).  Renormalising the gauge (`g := boxGauge / (1 + δ)`, which is again
`C^∞` off the centre) turns these two inclusions into exactly the hypotheses `hlow`/`hup` of the
box-sweep theorems: `PBox(t) ⊆ {g < t} ⊆ PBox((1+δ) t)` — this is
`Work.Smooth.Morse.Gauge.gaugeSandwich`, and with the smoothing
`Work.Smooth.Morse.Gauge.exists_smooth_gauge_with_sandwich` the gauge is `C^∞` as well.

Caveat: `boxGauge` is a norm and hence not smooth at the box centre `c`; the inclusion lemmas are
smoothness-free.  A `C^∞` gauge with the same sandwich is obtained by modifying `boxGauge` in a
neighbourhood of `c` (for instance replacing it by a smooth convex function there), which does not
change the sublevel sets `{boxGauge < t}` for the relevant values of `t` provided that
neighbourhood is contained in `{boxGauge < t}`; this smoothing step is *not* formalised here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

/-- **The `ℓ^{2k}`-gauge of Pardon's box**: a `C^∞` function away from the centre `c` whose
sublevel sets sandwich `Submission.PBox` with room `3^{1/(2k)}`. -/
def boxGauge (c : R3) (σ : Equiv.Perm (Fin 3)) (k : ℕ) (y : R3) : ℝ :=
  (∑ i : Fin 3, |(y (σ i) - c (σ i)) / Submission.boxSide i| ^ (2 * k)) ^
    (1 / (2 * (k : ℝ)))

end

end Work.Smooth.Morse
