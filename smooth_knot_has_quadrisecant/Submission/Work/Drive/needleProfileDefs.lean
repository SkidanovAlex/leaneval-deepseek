import Mathlib
import Submission.Work.Drive.needleStarShapedAux
import Submission.Work.Drive.chordSweepSmooth

/-!
# The chord frame of the needle and the loops' deviations

The needle `N = needleFam r D lam δ₁ δ₂ ε` is the double blur of the chamfered sweep loop.  Its
*chord side* is exactly the straight segment between the two `σ`-blurred endpoints of the retained
arc (`Work.Drive.sweepFam_chordZone`), and its *arc side* is the average of the retained arcs of the
loops in the window (`Work.Drive.sweepFam_arcZone`).  This module fixes the vocabulary of that
picture:

* `chordEndA`, `chordEndB` — the two `σ`-blurred endpoints of the needle's chord;
* `loopDev σ ξ` — the *deviation* of the retained arc of the loop at sweep parameter `σ` at fraction
  `ξ` from the chord of that loop: the vector whose positivity/non-vanishing is the O-avoidance
  content (`havoid`) for the raw loop;
* `arcFrac lam δ₁ t u` — the arc fraction at which the loop parameter `t - δ₁ * u` sits on the arc
  branch of the chamfered loop.

The key structural identity — proved in `Submission/Work/Drive/needleProfileDeviation.lean` — is
that the needle's deviation from its chord is the double average *of the loops' deviations*
`loopDev`, evaluated at the same fractions: the `σ`-blur does *not* have to be treated as a small
perturbation (it is not, uniformly in the box: see
`Submission/Work/Drive/NOTES_needleStarShapedDataProved.md`).
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- The `a`-endpoint of the needle's chord: the `σ`-blurred left endpoint of the retained arc. -/
def chordEndA (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (δ₂ ε : ℝ) : Space :=
  ∫ v in (-1 : ℝ)..1, sweepBump v • r (taR D (ε - δ₂ * v))

/-- The `b`-endpoint of the needle's chord: the `σ`-blurred right endpoint of the retained arc. -/
def chordEndB (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (δ₂ ε : ℝ) : Space :=
  ∫ v in (-1 : ℝ)..1, sweepBump v • r (tbR D (ε - δ₂ * v))

/-- The deviation of the retained arc of the loop at sweep parameter `σ` (at fraction `ξ`) from the
chord of that loop. -/
def loopDev (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (σ ξ : ℝ) : Space :=
  r (taR D σ + ξ * sweepW' D σ) - ((1 - ξ) • r (taR D σ) + ξ • r (tbR D σ))

/-- The arc fraction of the loop parameter `t - δ₁ * u` in the chamfered loop (on the arc branch). -/
def arcFrac (lam δ₁ t u : ℝ) : ℝ :=
  lam + (1 - 2 * lam) * (2 * sweepParam (t - δ₁ * u))

end Work.Drive
