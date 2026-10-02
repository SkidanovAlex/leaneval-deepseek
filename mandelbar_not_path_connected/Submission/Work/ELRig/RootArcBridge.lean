/-
# ELRig — the `RootArc` bridge by the crossing-parity route

`Submission/Work/Final/EL.lean` currently derives `RootArc.EquatorLeak` from
`Work.EL.equatorLeak`, whose signature consumes the *superseded* `Work.ELRig.RayLift` — a bundle
carrying the field `strand : RayStrand`, which is false in general (`NOTES.md` §6).

This file offers the drop-in replacement built on the crossing-parity route of §10: no lift data
at all, only the sibling bundles `nest` (ELNest/ELPull) and `tr` (ELNest/ELPull/ELTop).

It is deliberately *not* imported by `Submission.Work.ELRig.All`, so that the area's closure
stays free of the `Final` area.
-/
import Mathlib
import Submission.Work.ELRig.ParityEnd
import Submission.Work.Final.RootArc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELRig

/-- **The equator leak for a `RootArc`, by the crossing-parity route.**  This is the drop-in
replacement of `Work.Final.equatorLeak_of_ELRig`: it needs no `RayLift` (and hence no false
`RayStrand`), only the sibling-area bundles `nest` and `tr`. -/
theorem rootArc_equatorLeak {c : ℂ} (A : Work.Final.RootArc c)
    (nest : Work.EL.Z1Nest A.d.hN A.d.z₁ A.fl.Pa)
    (tr : Work.EL.B2Data A.d.hN A.d.z₁) : A.EquatorLeak :=
  Work.EL.equatorLeak_parity Work.TopJordan.jordanForm A.d A.fl nest tr

/-- **The `RootArc` bridge in the `Final` vocabulary**: `Work.Final.RootArc` gives
`Work.Final`'s `ELResiduals` from the two sibling bundles alone (no lift data). -/
theorem rootArc_equatorLeak_of_nestB2 {c : ℂ} (A : Work.Final.RootArc c)
    (nest : Work.EL.Z1Nest A.d.hN A.d.z₁ A.fl.Pa)
    (tr : Work.EL.B2Data A.d.hN A.d.z₁) :
    ∃ x : ℝ, A.fl.Ψ (x : ℂ) ∉ Work.EL.K c :=
  rootArc_equatorLeak A nest tr

end Work.ELRig

end
