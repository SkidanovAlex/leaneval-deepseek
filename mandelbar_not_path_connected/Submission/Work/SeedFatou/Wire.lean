/-
# `Work.SeedFatou` — wiring: what the root argument unlocks

`Work.SeedFatou.rootArcHeightZero` already discharges the `root` argument of
`Work.MandelFinal.finalInputs_of`.  This file records the two consequences a caller wants:

* `Work.SeedFatou.exists_rootParabolic_seedCert` — the certified seed produces a root-parabolic
  parameter `Work.EL.RootParabolic c`, with no hypothesis;
* `Work.SeedFatou.finalInputs_of_seed` / `Work.SeedFatou.mandelbar_not_path_connected_of_seed` —
  the final assembly and the endgame, with the `root` argument discharged here.  What remains is
  PARIMPL2's `LavaursInputs` (`hP`), GATE2's `TwoSided` (`hG`) and the degenerate half of Fatou's
  theorem (`hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate`, the area `FatouDeg`);
  substituting `Work.FatouDeg.fatouParabolicInput_degenerate` for `hDeg` makes the endgame
  unconditional in every classical input.
-/
import Mathlib
import Submission.Work.SeedFatou.RootArcHeightZero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedFatou

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The certified seed produces a root-parabolic parameter, with no hypothesis.**  This is the
whole chain of the root field: the seed `Work.MandelFinal.seedCert`, Böttcher's theorem
(`Work.SeedDyn.dynBottcherHomeo`), the strong Fatou form at the seed
(`Work.SeedFatou.fatouCritInBasin`, which supplies `crit` and `wake`) and the Jordan curve
theorem, wired by `Work.SeedExist.exists_rootParabolic_of_seedData`. -/
theorem exists_rootParabolic_seedCert : ∃ c : ℂ, Nonempty (Work.EL.RootParabolic c) := by
  obtain ⟨S⟩ := Work.SeedExist.ExplicitRootSeed.toData Work.MandelFinal.seedCert
  have hdyn : Work.ParamRays.DynBottcherHomeo S.c := Work.SeedDyn.dynBottcherHomeo S.mem
  exact Work.SeedExist.exists_rootParabolic_of_seedData S
    (Work.ParamRays.dynNakane hdyn)
    (Work.ParamRays.isDynBottcher_dynPhiOf hdyn.exists)
    (fatouCritInBasin S) Work.TopJordan.jordanForm

/-- **The final assembly, with the `root` argument discharged here.**  The only remaining
hypotheses are PARIMPL2's `LavaursInputs` (`hP`), GATE2's `TwoSided` (`hG`) and the degenerate half
of Fatou's theorem (`hDeg`); in particular `hDeg := Work.FatouDeg.fatouParabolicInput_degenerate`
gives `Work.Final.FinalInputs` outright. -/
noncomputable def finalInputs_of_seed (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate)
    {P : Work.PARIMPL.ParNormal (Work.FinalFix.arcOf rootArcHeightZero).d}
    {fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft (Work.FinalFix.c₀Of rootArcHeightZero))
      (Work.PARIMPL.gtc (Work.FinalFix.c₀Of rootArcHeightZero))
      (Work.FinalFix.arcOf rootArcHeightZero).d.z₁}
    {nIn : ℕ}
    (hP : Work.PARIMPL2.Lavaurs.LavaursInputs (Work.FinalFix.arcOf rootArcHeightZero).d P fl nIn)
    (hG : Work.GATE.TwoSided (Work.FinalFix.c₀Of rootArcHeightZero) P.Nm) :
    Work.Final.FinalInputs :=
  Work.MandelFinal.finalInputs_of rootArcHeightZero hP hG hDeg

/-- **The endgame, with the `root` argument discharged here**: modulo PARIMPL2's `LavaursInputs`
(`hP`), GATE2's `TwoSided` (`hG`) and the degenerate half of Fatou's theorem, the mandelbar is not
path connected. -/
theorem mandelbar_not_path_connected_of_seed
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate)
    {P : Work.PARIMPL.ParNormal (Work.FinalFix.arcOf rootArcHeightZero).d}
    {fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft (Work.FinalFix.c₀Of rootArcHeightZero))
      (Work.PARIMPL.gtc (Work.FinalFix.c₀Of rootArcHeightZero))
      (Work.FinalFix.arcOf rootArcHeightZero).d.z₁}
    {nIn : ℕ}
    (hP : Work.PARIMPL2.Lavaurs.LavaursInputs (Work.FinalFix.arcOf rootArcHeightZero).d P fl nIn)
    (hG : Work.GATE.TwoSided (Work.FinalFix.c₀Of rootArcHeightZero) P.Nm) :
    ¬ IsPathConnected Mandelbar :=
  Work.MandelFinal.mandelbar_not_path_connected_of rootArcHeightZero hP hG hDeg

end Work.SeedFatou

end
