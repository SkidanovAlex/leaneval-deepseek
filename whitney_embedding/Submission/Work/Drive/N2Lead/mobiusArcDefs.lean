import Mathlib
import Submission.Work.Drive.N2Lead.mobiusGeomDefs
import Submission.Work.Drive.N2Lead.modelArc_im_strictMonoOn

/-!
# Tier `D2d` (the Möbius saddle): coordinate lemmas for the model arcs

The curves themselves are `Work.Drive.N2Lead.mobiusRho`, `mobiusAlpha` and `mobiusBeta` of
`mobiusGeomDefs.lean`:

* `mobiusRho η δ s w = √(ζ w)`, `ζ w = σ(s,w) + i w` — the point of the right model arc of the level
  `Re ζ = s` in the chart coordinate `ζ = Z²`;
* `mobiusAlpha`/`mobiusBeta` — the two arcs of the *upper* level after the two slab twists
  `twistY a' (-1)` and `twistX ε (-1)`.

This file adds the coordinate `simp` lemmas and the pushed/twisted pair used by the assembly, plus
the rows of `SmoothTransition`-free smoothness needed to apply the compactness lemmas.

The two geometric lemmas about them are `Work.Drive.N2Lead.mobius_upperArcs` (sign separation of the
`y`-coordinates and `x`-monotonicity) and `Work.Drive.N2Lead.mobius_pushedStar` (the push makes the
angular rate have a constant sign).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- `mobiusRho` is the principal square root of the model `ζ`. -/
lemma mobiusRho_eq (η δ s w : ℝ) :
    mobiusRho η δ s w = Complex.sqrt ((Work.Drive.N2.saddleSigma η δ (s, w) : ℂ) + (w : ℂ) * Complex.I) :=
  rfl

/-- The imaginary part of `mobiusRho` is the strictly monotone model arc
`Work.Drive.N2Lead.modelArcIm` of `modelArc_im_strictMonoOn.lean`. -/
lemma mobiusRho_im (η δ s w : ℝ) : (mobiusRho η δ s w).im = modelArcIm η δ s w := rfl

/-- `mobiusRho` is the principal square root of `modelZeta`. -/
lemma mobiusRho_eq_sqrt_modelZeta (η δ s w : ℝ) : mobiusRho η δ s w = (modelZeta η δ s w).sqrt := rfl

/-- The two model arcs of the upper level, after the twists: the pair `(α, β)`. -/
noncomputable def mobiusArcTwisted (η δ s a' ε : ℝ) (w : ℝ) : E3 × E3 :=
  (mobiusAlpha η δ s a' ε w, mobiusBeta η δ s a' ε w)

/-- The two model arcs of the upper level after the twists and the vertical push `pushY D εp 1`. -/
noncomputable def mobiusArcPushed (η δ s a' ε D εp : ℝ) (w : ℝ) : E3 × E3 :=
  (pushY D εp 1 (mobiusAlpha η δ s a' ε w), pushY D εp 1 (mobiusBeta η δ s a' ε w))

lemma mobiusArcTwisted_fst (η δ s a' ε w : ℝ) :
    (mobiusArcTwisted η δ s a' ε w).1 = mobiusAlpha η δ s a' ε w := rfl

lemma mobiusArcTwisted_snd (η δ s a' ε w : ℝ) :
    (mobiusArcTwisted η δ s a' ε w).2 = mobiusBeta η δ s a' ε w := rfl

/-! ## Smoothness of the arcs (needed only to *apply* the two geometric lemmas)

The assembly applies `Work.Drive.N2Lead.mobius_pushedStar` to `mobiusAlpha`/`mobiusBeta`, whose
hypothesis is `ContDiff ℝ 1 g`.  That row is *not* stated here: `Complex.sqrt` is not smooth in the
Mathlib API (only `HasStrictDerivAt`/`DifferentiableAt` on `Complex.slitPlane`), and the model
`ζ w = σ(s,w) + i w` avoids the slit because `σ(s,w) = s > 0` for `|w| ≤ 2 - 4δ` and `Im ζ w = w ≠ 0`
for `|w| ≥ 2 - 4δ`.  It is supplied by the assembly's own file. -/

end

end Work.Drive.N2Lead
