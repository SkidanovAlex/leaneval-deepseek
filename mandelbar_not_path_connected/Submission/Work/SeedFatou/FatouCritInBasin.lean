/-
# `Work.SeedFatou` — Fatou's theorem in the strong form, at every `RootSeedData`

This is lemma B6 of `NOTES_LEAD_mandelbar_final2.md` §2.2: the two clauses of
`Work.SeedExist.FatouCritInBasin` at the seed are read off the packaged immediate-basin datum
`Work.SeedFatou.CritImmData` (`Work.SeedFatou.exists_critImm`), clause (i) by
`Work.SeedFatou.fatouCrit_clause_i` and clause (ii) by `Work.SeedFatou.fatouCrit_clause_ii`.

The result is stated for **every** `S : Work.SeedExist.RootSeedData`, not only for the certified
seed: no field of `RootSeedData` is used beyond those already consumed by `Work.SeedExist.flowerOf`
and by the two clause lemmas.  The certified seed itself enters only in
`Work.SeedFatou.rootArcHeightZero`.
-/
import Mathlib
import Submission.Work.SeedFatou.Defs
import Submission.Work.SeedFatou.exists_critImm
import Submission.Work.SeedFatou.fatouCrit_clause_i
import Submission.Work.SeedFatou.fatouCrit_clause_ii

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

/-- **Fatou's theorem in the strong form, at every `RootSeedData`** — the missing input `root` of
`Work.MandelFinal.finalInputs_of` (and of `Work.SeedExist.rootParabolicEL_of_seedData`), with no
hypothesis:

* (i) some `T_c`-iterate, of index `< 5`, of a point of the half-petal `Pg` of the flower lies in
  the connected component of `0` in the interior of the filled Julia set (`crit` of
  `Work.EL.RootParabolic`);
* (ii) some `F c`-iterate of the critical value `c` lies in some `T_c`-iterate, of index `< 5`, of
  `Pg` (`wake` of `Work.EL.RootParabolic`).

The phase — that the critical orbit converges to `z₁` itself and not to another point of the
5-cycle — is *not* part of this statement; it is proved downstream by
`Work.SeedExist.Fatou.mem_Pg_of_fatou` (see `Work.SeedExist.Wire.mem_Pg_of_seedData`). -/
theorem fatouCritInBasin (S : Work.SeedExist.RootSeedData) :
    Work.SeedExist.FatouCritInBasin S.c S.z₁ (Work.SeedExist.flowerOf S).Pg := by
  obtain ⟨D⟩ := exists_critImm S
  exact ⟨fatouCrit_clause_i S D, fatouCrit_clause_ii S D⟩

end Work.SeedFatou

end
