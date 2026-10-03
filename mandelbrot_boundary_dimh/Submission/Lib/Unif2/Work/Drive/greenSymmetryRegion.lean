import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.Drive.polarPtBasics
import Submission.Lib.Unif2.Work.Drive.cutoffProc

/-!
# The symmetry of the Green function of a region (`gA b = gB a`)

The target `Work.Drive.greenSymmetryRegion` is the crux of the whole project (see
`NOTES_greenSymmetryRegion_route.md`).  All the *planar* material (the polar coordinates, the
fundamental-solution reduction, the shear/flux layer) has been moved to
`Submission/Work/Drive/polarPtBasics.lean` (module `Submission.Work.Drive.polarPtBasics`) so that
the pole-identity modules can be built **without** importing this file (they cannot: importing it
would be a cycle).
-/

namespace Work.Drive

open MeasureTheory Set intervalIntegral

/-- **Symmetry (reciprocity) of the Green function of a region.** Let `Ω` be an open subset of a
connected, second countable `ℂ`-charted Riemann surface `X` with compact closure, let `a ≠ b` be
points of `Ω`, and let `gA` (resp. `gB`) be a Green function of `Ω` with pole `a` (resp. `b`) in the
sense of `Work.SimplyConnected.ABS.IsGreenOn` (positive and harmonic off the pole, unit logarithmic
pole at the pole, and superlevel sets with compact closure in `Ω`).  Then `gA b = gB a`, the
classical symmetry of the Green function (`G_Ω(a,b) = G_Ω(b,a)`).

Two candidates `gA`, `gA'` for the same pole differ by a harmonic function on `Ω` which is `< ε` off
a compact set for every `ε > 0`, hence vanish by the maximum principle, so `IsGreenOn` pins the
function down and the statement is well posed.

Classical proof (Green's identity / flux): on `R_ε = {gA > ε} ∖ (discs around a and b)`, the 1-form
`ω := gA ∗dgB - gB ∗dgA` is closed (pointwise computation using harmonicity), so its flux around
`∂R_ε` vanishes; the two small circles contribute `-2π gB a` and `+2π gA b` while the flux over
`{gA = ε}` is `ε`-small, whence `gA b = gB a`.  A Stokes-free route: write `ω = d(gA gB* - gB gA*)`
+ `(gA* dgB - gB* dgA)` using the local harmonic conjugates, and use that the mixed term has zero
flux (Cauchy's integral formula for the holomorphic 1-forms, plus a decomposition of `R_ε` along
cuts into simply connected pieces). -/
theorem greenSymmetryRegion {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {a b : X} (hab : a ≠ b) (ha : a ∈ Ω) (hb : b ∈ Ω)
    {gA gB : X → ℝ} (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB) :
    gA b = gB a :=
  Work.Drive.cutoffReciprocity hΩo hΩc hab ha hb hgA hgB

end Work.Drive
