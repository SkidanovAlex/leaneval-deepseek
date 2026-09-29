import Mathlib
import Submission.Work.TMC14Core.GapFind
import Submission.Work.TMC14Core.ratIdsFlat
import Submission.Work.TMC14Core.ratIdsVariation
import Submission.Work.TMC14Core.ratGapBound

/-!
# TMC14Core: the C14 theorem (`P_GapBound`)

The single entry point of this chapter.

`P_GapBound` (AJ Lemma 7.1 + Thm 7.2 in the form used for Thm 8.1(2)) says: for irrational
`α`, `0 < λ ≤ 1`, a window `[c,d] ⊆ Σ_α = amoSpec α lam` and `ε > 0` there are `δ > 0` and
`Q` such that for all `p : ℤ` and `q ≥ Q` with `|α - p/q| < δ/q` the density of states
`N_{p/q}` of the rational approximant has a *flat piece* in `[c,d]` of length at least
`e^{-εq}λ^{q/2}`.

The chapter proves it in the form the component DAG prescribes (C14 consumes C4, C5, C6, C7):

    p_gapBound (h4 : P_LEBasics) (h5 : P_RotBasics) (h6 : P_IDSSpectrum) (h7 : P_BJ) :
      P_GapBound

The three rational-approximant inputs of ROUTE_LEAD §4 C14 are proved in this directory:

* `ratIdsFlat`      — 14b: `N_{p/q}` is constant on the gaps of `ratSpec p q lam`;
* `ratIdsVariation` — 14c: across a band of `ratSpec p q lam`, `N_{p/q}` grows by `1/q'`,
  `q' = q / gcd(p,q)`;
* `ratGapBound`     — 14e + 14f + 14g: the Choi–Elliott–Yui gap estimate.

The gap-finding argument 14d + 14g, together with the two elementary facts
`ratDenomLarge` and `ratGapEndpoints`, is in `GapFind.lean`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-- **C14 (`P_GapBound`), reduced form.**  From the two general inputs `P_LEBasics`,
`P_BJ`, the continuity/monotonicity inputs `P_RotBasics`, `P_IDSSpectrum`, and the three
rational-approximant facts `RatIdsFlat` (14b), `RatIdsVariation` (14c), `RatGapBound`
(14e + 14f). -/
theorem p_gapBound_reduced (h4 : P_LEBasics) (h5 : P_RotBasics) (h6 : P_IDSSpectrum)
    (h7 : P_BJ) (hA : RatIdsFlat) (hB : RatIdsVariation) (hD : RatGapBound) : P_GapBound :=
  p_gapBound_of h4 h5 h6 h7 hA hB hD

/-- **C14 (`P_GapBound`).**

For irrational `α`, `0 < λ ≤ 1`, a window `[c,d] ⊆ amoSpec α lam` and `ε > 0` there are
`δ > 0` and `Q` such that every `p : ℤ` and `q ≥ Q` with `|α - p/q| < δ/q` admit
`c ≤ a' < b' ≤ d` with `b' - a' ≥ e^{-εq} λ^{q/2}` and `N_{p/q}(a') = N_{p/q}(b')`.

This is component C14 of the Ten Martini formalisation, in the form of the component DAG
(C14 consumes C4 `P_LEBasics`, C5 `P_RotBasics`, C6 `P_IDSSpectrum`, C7 `P_BJ`). -/
theorem p_gapBound (h4 : P_LEBasics) (h5 : P_RotBasics) (h6 : P_IDSSpectrum) (h7 : P_BJ) :
    P_GapBound :=
  p_gapBound_of h4 h5 h6 h7 ratIdsFlat ratIdsVariation ratGapBound

end Work.TMC14Core
