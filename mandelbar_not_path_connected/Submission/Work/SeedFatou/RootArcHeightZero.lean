/-
# `Work.SeedFatou` — the root argument of `Work.MandelFinal.finalInputs_of`, with no hypothesis

This is lemma B7 of `NOTES_LEAD_mandelbar_final2.md` §2.2.  Chaining

* the certified seed `Work.MandelFinal.seedCert : Work.SeedExist.ExplicitRootSeed`,
* `Work.SeedExist.ExplicitRootSeed.toData`,
* Böttcher's theorem in the dynamical plane at a Mandelbar parameter
  (`Work.SeedDyn.dynBottcherHomeo`),
* the strong Fatou form at the seed `Work.SeedFatou.fatouCritInBasin`,
* the Jordan curve theorem `Work.TopJordan.jordanForm`,

through `Work.MandelFinal.rootArcHeightZero_of_seedData` produces the `root` argument
`Work.FinalFix.RootArcHeightZero` of `Work.MandelFinal.finalInputs_of` unconditionally: nothing
about the critical orbit, the wake, the petal or the height is assumed.

Consequently `Work.MandelFinal.mandelbar_not_path_connected_of` needs only `hP` (PARIMPL2) and
`hG` (GATE2).
-/
import Mathlib
import Submission.Work.SeedFatou.FatouCritInBasin
import Submission.Work.MandelFinal.All
import Submission.Work.SeedDyn.Main
import Submission.Work.TopJordan.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedFatou

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The root argument of `Work.MandelFinal.finalInputs_of`, with no hypothesis.** -/
theorem rootArcHeightZero : Work.FinalFix.RootArcHeightZero := by
  obtain ⟨S⟩ := Work.SeedExist.ExplicitRootSeed.toData Work.MandelFinal.seedCert
  have hdyn : Work.ParamRays.DynBottcherHomeo S.c := Work.SeedDyn.dynBottcherHomeo S.mem
  exact Work.MandelFinal.rootArcHeightZero_of_seedData S
    (Work.ParamRays.dynNakane hdyn)
    (Work.ParamRays.isDynBottcher_dynPhiOf hdyn.exists)
    (fatouCritInBasin S) Work.TopJordan.jordanForm

end Work.SeedFatou

end
