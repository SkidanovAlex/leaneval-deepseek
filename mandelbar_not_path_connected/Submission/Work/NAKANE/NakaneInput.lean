/-
# `NakaneInput` from the local-homeomorphism input alone

This module is **not** part of `Submission.Work.NAKANE.All` (it imports `Work.Final.Glue`, another
area's module); import it only where `Work.Final` is already available.

It packages the two halves of the NAKANE contract into the single structure `Work.Final` consumes:

  `Work.ParamRays.NakaneInput`  from  `Work.NAKANE.PhiLocalHomeo` (R1) alone,

using `Work.NAKANE.nakaneHomeo_of_localHomeo` (`...NAKANE.Assembly`) for the homeomorphism field and
the unconditional `Work.NAKANE.uniformBottcherAsymptotic` (`...NAKANE.Asymptotic`) for the uniform
asymptotic field; the `bottcher` field is discharged by `Work.Bottcher.bottcherExists_crit`.
-/
import Submission.Work.NAKANE.Assembly
import Submission.Work.Final.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Nakane's classical input bundle `Work.ParamRays.NakaneInput` from (R1) alone.** -/
theorem nakaneInput_of_localHomeo (hloc : PhiLocalHomeo) : Work.ParamRays.NakaneInput :=
  Work.Final.nakane_of_homeo_asymptotic (nakaneHomeo_of_localHomeo hloc)
    uniformBottcherAsymptotic

end Work.NAKANE
