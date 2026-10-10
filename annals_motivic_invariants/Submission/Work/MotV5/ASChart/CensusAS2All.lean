import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotC5N3.Assembly
import Submission.Work.MotV5.ASChart.chartIsoAS2
import Submission.Work.MotV5.CensusAux.fAS_notMem_pe

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.ASChart.CensusAS2All` — the corrected AS census, via the generic census

Since 2026-10-07 (lead's order **D1**, `Submission/Work/MOTIVIC_INTEGRATION_AUDIT.md` §4) the
census is taken from the **generic** chapter `Submission/Work/MotC5N3/` instead of assembling the
`RatFunc 𝕜`-only clauses of `MotAS` by hand.  The generic statement

`Work.MotC5N3.CensusAS2Gen (RatFunc 𝕜) D hD (Work.MotV.fAS 𝕜)`

is *definitionally* `Work.MotAS.CensusAS2 D hD` (same eleven conjuncts, with the class specialised
to `g = fAS 𝕜 = X³ + X` and the base ring to `K = RatFunc 𝕜`), and
`Work.MotC5N3.censusAS2Gen` produces it from the generic clauses for any `g ∉ ℘(K)`; the sole
extra input is `Work.MotV5.CensusAux.fAS_notMem_pe 𝕜` (`fAS ∉ ℘(RatFunc 𝕜)`).

This file therefore no longer imports `CensusAS2Core` (nor, through it,
`MotAS.censusAS2_class_sAS` / `ASRulingDiv2` / `ASZTwistDiv2`): the `RatFunc`-only `MotAS` census
is retired by this bridge.  The old hand-assembly survives, unused, in
`Work.MotV5.ASChart.censusAS2_of_chartIso` (`CensusAS2Core.lean`), and the chart isomorphism
`Work.MotV5.ASChart.chartIsoAS2` is still a headline result of this subproject.

The other `MotV5`-side pieces of that older route (`ASLocal.ClassSdual`, `ASLocal.asTheta2_ker`,
`ASLocal.asTheta2_fracTop`, `ASLocal.asPhi2_rho_ne_zero`, the `ASLocal.asRuleQ_*` certificates) are
likewise off the path now; they are kept as reserves (see `STATUS.md` §18).
-/

set_option autoImplicit false

namespace Work.MotV5.ASChart

open Work.MotV

/-- **The corrected AS census, unconditionally**, from the generic census of `MotC5N3`. -/
theorem censusAS2_all (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) : Work.MotAS.CensusAS2 D hD :=
  Work.MotC5N3.censusAS2Gen (RatFunc 𝕜) D hD (Work.MotV.fAS 𝕜)
    (by simpa [Work.MotV.fAS] using Work.MotV5.CensusAux.fAS_notMem_pe 𝕜)

/-- **Node `LK_AS′`, unconditionally**: the Crauder–Katz link certificate between the two
Artin–Schreier twists of the Klein curve, in the explicit Galois-coordinate model
`Work.MotAS.twistFieldAS`. -/
theorem linkCertAS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    Nonempty (Work.MotV.LinkCert (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
      ↥(Work.MotAS.twistFieldAS D (2 • Work.MotV.fAS 𝕜))) :=
  Work.MotAS.linkCertAS_of_censusAS2 D hD (censusAS2_all 𝕜 D hD)

end Work.MotV5.ASChart
