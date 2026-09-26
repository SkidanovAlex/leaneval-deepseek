import Mathlib
import Submission.BandArcCover
import Submission.Work.Drive.chordSweepDefs

/-!
# The smoothed chord sweep: concrete definitions

This module fixes *concrete* formulas for the family of knots of the "sweep through embeddings"
proof of `Work.Drive.unknotted_of_chordSweep`, so that the analytic statements about it can be
stated without any existential over families.

* `Work.Drive.clampI`, `Work.Drive.taR`, `Work.Drive.tbR` — the lift data of
  `Work.Drive.SweepData` extended to real parameters (clamped to `[0,1]`), so that the sweep
  parameter can be smoothed.
* `Work.Drive.sweepArc'`, `Work.Drive.sweepChord'` — the arc side and the chord side.
* `Work.Drive.sweepLoopChamfer r D lam s t` — the raw loop at parameter `s`, with the two corners
  cut off by straight *chamfers* at the parameter offset `lam` (a fixed fraction of the retained
  arc): the arc side runs from `ξ = lam` to `ξ = 1 - lam`, and the chord side runs back from
  `ξ = 1 - lam` to `ξ = lam`, the two joined by the chamfer segments.  The corners of this loop
  have *definite* angles (the arc's tangent against the transverse chamfer direction), which is
  what keeps the velocity of the smoothed loop bounded below.
* `Work.Drive.sweepBump` — a `C^∞` bump supported in `[-1,1]`, positive inside.
* `Work.Drive.sweepSmoothT` — the convolution of the raw loop in the *loop parameter* (this makes
  every slice `C^∞`);
* `Work.Drive.sweepFam` — the further convolution in the *sweep parameter* (this makes the
  dependence on the sweep parameter `C^∞`);
* `Work.Drive.sweepNeedle r D lam δ ε` — the "needle" slice at parameter `ε`, i.e. the smoothed
  loop at `ε` (a thin lens for small `ε`).
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

/-- The unit interval as a subtype of `ℝ`, entered by clamping. -/
def clampI (x : ℝ) : I := ⟨min 1 (max 0 x),
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩⟩

/-- The `a`-branch lift, extended to all real parameters by clamping. -/
def taR {d : BandArcData} (D : SweepData d) (x : ℝ) : ℝ := D.ta (clampI x)

/-- The `b`-branch lift, extended to all real parameters by clamping. -/
def tbR {d : BandArcData} (D : SweepData d) (x : ℝ) : ℝ := D.tb (clampI x)

/-- The width of the retained arc, as a function of a real parameter. -/
def sweepW' {d : BandArcData} (D : SweepData d) (x : ℝ) : ℝ := tbR D x - taR D x

/-- The point at fraction `ξ` of the retained arc at sweep parameter `s`. -/
def sweepArc' (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s ξ : ℝ) : Space :=
  r (taR D s + ξ * sweepW' D s)

/-- The point at fraction `ξ` of the chord at sweep parameter `s`. -/
def sweepChord' (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (s ξ : ℝ) : Space :=
  (1 - ξ) • r (taR D s) + ξ • r (tbR D s)

/-- **The chamfered sweep loop.**  For the loop parameter `t` with fraction
`u = sweepParam t ∈ [0,1)`: on `[0,1/2]` the arc side from `ξ = lam` to `ξ = 1 - lam`; on
`[1/2, 1/2 + lam/2]` the straight chamfer from the arc's point at `ξ = 1-lam` to the chord's
point at `ξ = 1-lam`; on `[1/2+lam/2, 1-lam/2]` the chord side back from `ξ = 1-lam` to
`ξ = lam`; and on `[1-lam/2, 1]` the chamfer from the chord's point at `ξ = lam` to the arc's
point at `ξ = lam`.  The result is continuous and `period`-periodic in `t`. -/
def sweepLoopChamfer (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam : ℝ)
    (s t : ℝ) : Space :=
  let u := sweepParam t
  if u ≤ 1 / 2 then sweepArc' r D s (lam + (1 - 2 * lam) * (2 * u))
  else if u ≤ 1 / 2 + lam / 2 then
    (1 - (2 * u - 1) / lam) • sweepArc' r D s (1 - lam)
      + ((2 * u - 1) / lam) • sweepChord' r D s (1 - lam)
  else if u ≤ 1 - lam / 2 then
    sweepChord' r D s ((1 - lam) - ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
  else
    (1 - (u - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
      + ((u - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam

/-- A `C^∞` bump function supported in `[-1,1]`, positive in the interior. -/
def sweepBump (u : ℝ) : ℝ := Real.smoothTransition (1 + u) * Real.smoothTransition (1 - u)

/-- The raw loop convolved in the *loop parameter*: every slice is `C^∞` in `t`. -/
def sweepSmoothT (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ : ℝ)
    (s t : ℝ) : Space :=
  ∫ u in (-1)..1, sweepBump u • sweepLoopChamfer r D lam s (t - δ * u)

/-- The loop family convolved in the *sweep parameter* as well: joint `C^∞` dependence. -/
def sweepFam (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ : ℝ)
    (s t : ℝ) : Space :=
  ∫ v in (-1)..1, sweepBump v • sweepSmoothT r D lam δ₁ (s - δ₂ * v) t

/-- **The needle**: the smoothed loop at sweep parameter `ε`. -/
def sweepNeedle (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ ε : ℝ) :
    ℝ → Space := fun t => sweepSmoothT r D lam δ₁ ε t

/-- A smooth "easing" function on `[0,1]`: `gluePsi s = 3 s^2 - 2 s^3`, with
`gluePsi 0 = 0`, `gluePsi 1 = 1` and `gluePsi' 0 = gluePsi' 1 = 0`. -/
def gluePsi (s : ℝ) : ℝ := s ^ 2 * (3 - 2 * s)

/-- **Concatenation of two one-parameter families**, with the parameter eased so that the
`s`-derivative vanishes at the junction `s = 1/2` from both sides: this makes the concatenation
jointly `C¹` whenever both families are. -/
def sweepGlue (F G : ℝ → ℝ → Space) (s t : ℝ) : Space :=
  if s ≤ 1 / 2 then F t (gluePsi (2 * s)) else G t (gluePsi (2 * s - 1))

/-- The slice of the fully smoothed family `sweepFam` at sweep parameter `ε`: this is the
"needle" in the form in which the needle-to-circle family consumes it. -/
def sweepNeedleFam (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε : ℝ) :
    ℝ → Space := fun t => sweepFam r D lam δ₁ δ₂ ε t

/-- The model circle in the plane of the chord at the needle's parameter: the circle whose
diameter is the chord from `r (ta ε)` to `r (tb ε)`. -/
def sweepModelCircle (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (ε : ℝ)
    (f1 f2 : Space) (t : ℝ) : Space :=
  (1 / 2 : ℝ) • (r (taR D ε) + r (tbR D ε)) +
    ((‖r (tbR D ε) - r (taR D ε)‖ / 2) • (Real.cos t • f1 + Real.sin t • f2))

end Work.Drive
