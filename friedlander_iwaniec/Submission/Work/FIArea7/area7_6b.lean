/-
# `Submission.Work.FIArea7.area7_6b` — the amended round-6 area 7 (`Work.FITop4.Area7_6b`)

This is the deliverable of area 7 after the lead's contract amendment
(`AREA7_ROUTE_LEAD.md`, `Submission/Work/FITop4/Areas6c.lean`).  `Area7_6b` is `Area7_6` plus the
two hypotheses the composition supplies — `Pa.τ = tauOf Pa.x Asave` and an axis-free polar box —
and `Submission/Work/FIRed6Axis/prop41_of_areas6c.lean` is **proved** and consumes exactly
`h7 : Work.FITop4.Area7_6b`.

The proof is

    area7_6b_of_uniform_of_strip (Area7Uni6B_of_pieces prop172UnconditionalB) strip_bound6

run on the clash-free copies `Submission/Work/FIArea7CF/` (NOTES §61.1, §63):

* `Work.FIArea7CF.Area7AssemblyB` assembles `Area7Uni6B` — the paper's Proposition 17.3 (17.19) at
  the uniform cut with the amended hypotheses and the range cap `X ≤ (log N)^{nuU}` — from the
  *FI* §17 bridge: `isBetaCoeff6_split` (A2), `uniSChar_betaL_le` (A5, the deep input at the
  shifted frequencies), `charRegionLowSlackUse_le`, `charRegionLow_pair_sharp_le` (A6),
  `charRegionLow_split_le` (A7), `deltaTau_mass_le` (A3), `deltaQ_mass_le` (A4),
  `regionHighSlack_le` (region II with the mode slack), `NumericCoreB` (the real-variable
  bookkeeping), plus the engine, the guard, the caps, the strip and the trivial regime
  `area7_small_theta`;
* `Work.FIArea7CF.Prop172B` supplies `Prop172Classical`: it is the composition of
  `Work.FIArea7.prop172Unconditional` but with the *proved* (21.9) instead of its interface (the two
  declarations of `holder6_bound` collide).  The underlying modules are *FI* Proposition 17.2 in the paper's own form, proved from
  *FI* §§21–26 (`prop213Pub`, `prop214`, `prop231`, `prop232Done`, `theorem2psi`).

The regime `θ²τX ≤ 1` is `area7_small_theta` (it is *not* optional: with an arbitrary `A'`
the mode length `modeLen = ⌈θ⁻¹⌉·X·⌈log(N+2)⌉⁶` need not be a polylogarithm, and `A3`/`A4` are
only affordable in the complement `θ²τX > 1`, where `τ = tauOf Pa.x Asave` gives
`modeLen ≤ (log N)^{5·10⁹}`).  See `AREA7_ROUTE_LEAD.md` §2.2 (A8) and `NOTES.md` §61–§63.
-/
import Mathlib
import Submission.Work.FITop4.Areas6c
import Submission.Work.FIArea7CF.Area7AssemblyB
import Submission.Work.FIArea7CF.Prop172B

set_option autoImplicit false

namespace Work.FIArea7

/-- **The amended round-6 contract of area 7** (the deliverable of this file). -/
theorem area7_6b : Work.FITop4.Area7_6b :=
  area7_6b_of_uniform_of_strip (Area7Uni6B_of_pieces prop172UnconditionalB) strip_bound6

end Work.FIArea7
