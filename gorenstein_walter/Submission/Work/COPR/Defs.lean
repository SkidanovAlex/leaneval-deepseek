/-
# AREA COPR — definitions (re-export of the canonical `Work.GW2` vocabulary)

The shared vocabulary of the project (`Work.GW2`: `oddCore`, `pCore`, `fitting`, `invSet`,
`IsHallIn`, `FeitThompsonProp`, …) and the contract `Prop`s — including the six of this area
(`Coprime11iProp`, `Coprime11iiProp`, `Coprime11iiiProp`, `Coprime11ivProp`, `Coprime13Prop`,
`Coprime15Prop`) — have their canonical home in `Submission/Work/ASM/Defs.lean` (copied there
verbatim from `Submission/Work/_design_gw/Contracts2.lean`).

This module re-exports that vocabulary, so that `import Submission.Work.COPR.Defs` (used by the
component proofs of this area) resolves as before, and so that the results of this area can be
imported in the same environment as `Work.GW2.LocalToolkit`.  Nothing is redefined here: defining the
`Work.GW2` names again would clash with `ASM.Defs`.

The deliverable of this area is `Work.GW2.coprime11i`, `coprime11ii`, `coprime11iii`,
`coprime11iv`, `coprime13`, `coprime15` and the bundle `Work.GW2.coprimeArea`
(`Submission.Work.COPR.Deliverable`); the content lives in `Submission.Work.COPR.Glue`,
`Coprime11i`, `Involution`, `InvSet` and the component modules of this directory.

NOTE.  The pre-existing seed file `Submission/Work/Coprime/Basic.lean` (area `Work.Coprime`, from an
earlier drive) **does not compile on Lean v4.35.0-rc3** (three errors in `mem_fixedIn`,
`inv_mem_invSet` and `conjAut.map_mul'`).  It is another area's file, so it is not edited here; the
involution API of that area is re-derived, with the same names and conventions, in
`Submission.Work.COPR.Involution` (namespace `Work.COPR`).
-/
import Submission.Work.ASM.Defs
