/-
# `Work.MandelFinal.FinalAssembly` — the assembly with the root field discharged from the seed

Area `Submission/Work/MandelFinal/`.  This module substitutes the certified seed
`Work.MandelFinal.seedCert` (`Submission/Work/MandelFinal/seedCert.lean`) into
`Work.MandelFinal.rootArcHeightZero_of`, so that **the root-arc data of the final assembly is
produced here** and the caller no longer has to supply it.

`Work.MandelFinal.rootArcHeightZero_of_fatou` is the exact statement of what `root` still needs:
the strong form of the classical Fatou result at the seed,
`Work.SeedExist.FatouCritInBasin` (the fields `crit` and `wake` of `Work.EL.RootParabolic`).  It
is the single external input of the area `SeedExist`; see `NOTES.md` §"the root field".
-/
import Submission.Work.MandelFinal.Root
import Submission.Work.SeedExist.Wire
import Submission.Work.MandelFinal.seedCert
import Submission.Work.MandelFinal.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.MandelFinal

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The root-arc data of the assembly, from the certified seed alone** — modulo the one input
that the current tree does not produce: the strong form of Fatou's theorem at the seed. -/
theorem rootArcHeightZero_of_fatou
    (hfat : ∀ (c z : ℂ) (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c)
      ((Tantibar c)^[5]) z), c ∈ Mandelbar → Work.SeedExist.FatouCritInBasin c z fl.Pg) :
    Work.FinalFix.RootArcHeightZero :=
  rootArcHeightZero_of seedCert hfat

/-- **The final assembly with `root` discharged from the certified seed**: the two live exports
`LavaursInputs` (PARIMPL2) and `Work.GATE.TwoSided` (GATE2), plus the two classical inputs
`FatouParabolicInput_degenerate` and `RotationNumberZero (1/4) 1`, give
`Work.Final.FinalInputs` — the root-arc data being produced internally from
`Submission/Work/MandelFinal/seedCert.lean`.

Note the (unavoidable) dependence of the PARIMPL2/GATE2 data on the value of
`Work.FinalFix.c₀Of (rootArcHeightZero_of_fatou hfat)`: it is the FQC-transported parameter of the
height shift, and it is the only parameter at which those data are needed. -/
noncomputable def finalInputs_of_fatou
    (hfat : ∀ (c z : ℂ) (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c)
      ((Tantibar c)^[5]) z), c ∈ Mandelbar → Work.SeedExist.FatouCritInBasin c z fl.Pg)
    {P : Work.PARIMPL.ParNormal (Work.FinalFix.arcOf (rootArcHeightZero_of_fatou hfat)).d}
    {fl : Work.FatouCoordFix.ParabolicFlowerFix
      (Work.PARIMPL.Ft (Work.FinalFix.c₀Of (rootArcHeightZero_of_fatou hfat)))
      (Work.PARIMPL.gtc (Work.FinalFix.c₀Of (rootArcHeightZero_of_fatou hfat)))
      (Work.FinalFix.arcOf (rootArcHeightZero_of_fatou hfat)).d.z₁}
    {nIn : ℕ}
    (hP : Work.PARIMPL2.Lavaurs.LavaursInputs
      (Work.FinalFix.arcOf (rootArcHeightZero_of_fatou hfat)).d P fl nIn)
    (hG : Work.GATE.TwoSided (Work.FinalFix.c₀Of (rootArcHeightZero_of_fatou hfat)) P.Nm)
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate) :
    Work.Final.FinalInputs :=
  finalInputs_of (rootArcHeightZero_of_fatou hfat) hP hG hDeg

/-- **The endgame with `root` discharged from the certified seed**: `¬ IsPathConnected Mandelbar`
from the two live exports and the two classical inputs. -/
theorem mandelbar_not_path_connected_of_fatou
    (hfat : ∀ (c z : ℂ) (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c)
      ((Tantibar c)^[5]) z), c ∈ Mandelbar → Work.SeedExist.FatouCritInBasin c z fl.Pg)
    {P : Work.PARIMPL.ParNormal (Work.FinalFix.arcOf (rootArcHeightZero_of_fatou hfat)).d}
    {fl : Work.FatouCoordFix.ParabolicFlowerFix
      (Work.PARIMPL.Ft (Work.FinalFix.c₀Of (rootArcHeightZero_of_fatou hfat)))
      (Work.PARIMPL.gtc (Work.FinalFix.c₀Of (rootArcHeightZero_of_fatou hfat)))
      (Work.FinalFix.arcOf (rootArcHeightZero_of_fatou hfat)).d.z₁}
    {nIn : ℕ}
    (hP : Work.PARIMPL2.Lavaurs.LavaursInputs
      (Work.FinalFix.arcOf (rootArcHeightZero_of_fatou hfat)).d P fl nIn)
    (hG : Work.GATE.TwoSided (Work.FinalFix.c₀Of (rootArcHeightZero_of_fatou hfat)) P.Nm)
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate) :
    ¬ IsPathConnected Mandelbar :=
  Work.Final.mandelbar_not_path_connected_of_inputs
    (finalInputs_of_fatou hfat hP hG hDeg)

/-- **The assembly with the *pointed* Fatou input.**  This is the weakest form of the root input
available: a single `Work.SeedExist.FatouCritInBasin` instance at one seed data set (the input that
`Work.MandelFinal.rootArcHeightZero_of_seedData` consumes), instead of the global form `hfat`.  The
root argument is then `rootArcHeightZero_of_seedData S hN hbott hfat hJ` and the PARIMPL2/GATE2 data
are read at it. -/
noncomputable def finalInputs_of_seedData (S : Work.SeedExist.RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c))
    (hbott : Work.ParamRays.IsDynBottcher S.c (Work.ParamRays.dynPhiOf S.c))
    (hfat : Work.SeedExist.FatouCritInBasin S.c S.z₁ (Work.SeedExist.flowerOf S).Pg)
    (hJ : Work.Top.JordanForm)
    {P : Work.PARIMPL.ParNormal
      (Work.FinalFix.arcOf (rootArcHeightZero_of_seedData S hN hbott hfat hJ)).d}
    {fl : Work.FatouCoordFix.ParabolicFlowerFix
      (Work.PARIMPL.Ft (Work.FinalFix.c₀Of (rootArcHeightZero_of_seedData S hN hbott hfat hJ)))
      (Work.PARIMPL.gtc (Work.FinalFix.c₀Of (rootArcHeightZero_of_seedData S hN hbott hfat hJ)))
      (Work.FinalFix.arcOf (rootArcHeightZero_of_seedData S hN hbott hfat hJ)).d.z₁}
    {nIn : ℕ}
    (hP : Work.PARIMPL2.Lavaurs.LavaursInputs
      (Work.FinalFix.arcOf (rootArcHeightZero_of_seedData S hN hbott hfat hJ)).d P fl nIn)
    (hG : Work.GATE.TwoSided
      (Work.FinalFix.c₀Of (rootArcHeightZero_of_seedData S hN hbott hfat hJ)) P.Nm)
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate) :
    Work.Final.FinalInputs :=
  finalInputs_of (rootArcHeightZero_of_seedData S hN hbott hfat hJ) hP hG hDeg

/-- The endgame from the pointed Fatou input. -/
theorem mandelbar_not_path_connected_of_seedData (S : Work.SeedExist.RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c))
    (hbott : Work.ParamRays.IsDynBottcher S.c (Work.ParamRays.dynPhiOf S.c))
    (hfat : Work.SeedExist.FatouCritInBasin S.c S.z₁ (Work.SeedExist.flowerOf S).Pg)
    (hJ : Work.Top.JordanForm)
    {P : Work.PARIMPL.ParNormal
      (Work.FinalFix.arcOf (rootArcHeightZero_of_seedData S hN hbott hfat hJ)).d}
    {fl : Work.FatouCoordFix.ParabolicFlowerFix
      (Work.PARIMPL.Ft (Work.FinalFix.c₀Of (rootArcHeightZero_of_seedData S hN hbott hfat hJ)))
      (Work.PARIMPL.gtc (Work.FinalFix.c₀Of (rootArcHeightZero_of_seedData S hN hbott hfat hJ)))
      (Work.FinalFix.arcOf (rootArcHeightZero_of_seedData S hN hbott hfat hJ)).d.z₁}
    {nIn : ℕ}
    (hP : Work.PARIMPL2.Lavaurs.LavaursInputs
      (Work.FinalFix.arcOf (rootArcHeightZero_of_seedData S hN hbott hfat hJ)).d P fl nIn)
    (hG : Work.GATE.TwoSided
      (Work.FinalFix.c₀Of (rootArcHeightZero_of_seedData S hN hbott hfat hJ)) P.Nm)
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate) :
    ¬ IsPathConnected Mandelbar :=
  Work.Final.mandelbar_not_path_connected_of_inputs
    (finalInputs_of_seedData S hN hbott hfat hJ hP hG hDeg)

end Work.MandelFinal
