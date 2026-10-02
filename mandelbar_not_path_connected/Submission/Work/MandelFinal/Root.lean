/-
# `Work.MandelFinal.Root` — the `root` field of `FinalInputs`, modulo the strong Fatou input

Area `Submission/Work/MandelFinal/`.  This module builds the root-arc data
`Work.FinalFix.RootArcHeightZero = ∃ c, ∃ A : Work.Final.RootArc c, A.critHeight = 0` from

* the certified seed `Work.SeedExist.ExplicitRootSeed` (area `SeedCertNum` + `SeedCertRay`,
  assembled in `Submission/Work/MandelFinal/SeedCert.lean`), and
* the **strong form of Fatou's theorem at the seed**
  `Work.SeedExist.FatouCritInBasin` (see `NOTES.md` §"the root field" for why this input is
  unavoidable with the current tree).

The chain is the ledger's route E:

```
ExplicitRootSeed
  → Work.SeedExist.rootParabolicEL_of_explicitSeed        (Böttcher homeomorphism: SeedDyn;
      Jordan curve theorem: TopJordan; strong Fatou: FatouCritInBasin)
  → d : Work.EL.RootParabolic c
  → Work.FlowerGlue.exists_petalInput d            (PetalInput for a repaired flower)
  → Work.FQCInputs.shiftFlower / petalShift / phase_normalised   (MNS phase normalisation)
  → Work.FQCInputs.simpleTransfer_all              (the petal-direction input: PROVED)
  → Work.FlowerGlue.RootArcHeightZero_of_seed      (the MNS height shift, with the
      uniqueness Work.FlowerGlue.fatouUnique discharged)
```

The only non-delivered input is `FatouCritInBasin`: it is what supplies the fields `crit` and
`wake` of `Work.EL.RootParabolic` (the critical orbit of `F c` converging to `z₁` and the L-wake
condition) and it is the single external input of the area `SeedExist`.
-/
import Submission.Work.MandelFinal.Classical
import Submission.Work.SeedExist.Wire
import Submission.Work.SeedDyn.Main
import Submission.Work.TopJordan.Main
import Submission.Work.FlowerGlue.SameWitness
import Submission.Work.FlowerGlue.PetalInput
import Submission.Work.FQCInputs.HeightShift
import Submission.Work.FQCInputs.simpleTransfer_all

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

/-- **The height shift at *any* root-parabolic parameter — no hypothesis.**

The whole FQC/FatouCoord/FlowerGlue part of the root field is proved: from a
`Work.EL.RootParabolic c` the repaired Leau–Fatou flower
(`Work.FlowerGlue.exists_petalInput`), the petal input, MNS's phase normalisation
(`Work.FQCInputs.shiftFlower`, `phase_normalised`), the petal-direction input
(`Work.FQCInputs.simpleTransfer_all`, the continuation argument, no hypothesis) and the height
shift to `0` (`Work.FlowerGlue.RootArcHeightZero_of_seed`, with the Fatou-coordinate uniqueness
`Work.FlowerGlue.fatouUnique`) produce root-arc data of critical Écalle height `0`.

Consequently **the only missing input of the root field is `Work.EL.RootParabolic` itself**, i.e.
the `crit` and `wake` fields (see `NOTES.md` §2). -/
theorem rootArcHeightZero_of_rootParabolic {c : ℂ} (d : Work.EL.RootParabolic c) :
    Work.FinalFix.RootArcHeightZero := by
  obtain ⟨fl₀, hpetal₀⟩ := Work.FlowerGlue.exists_petalInput d
  obtain ⟨hpetal₀⟩ := hpetal₀
  refine Work.FlowerGlue.RootArcHeightZero_of_seed d
    (Work.FQCInputs.shiftFlower (Work.FQCInputs.phaseShift d fl₀.toParabolicFlower)
      fl₀.toParabolicFlower) ?_ ?_ ?_
  · exact Work.FQCInputs.petalShift hpetal₀ _
  · exact Work.FQCInputs.phase_normalised d fl₀.toParabolicFlower
  · exact Work.FQCInputs.simpleTransfer_all d _ _

/-- **The root-arc parameter from the certified seed**, modulo the strong Fatou input
`Work.SeedExist.FatouCritInBasin`.

The parameter of the resulting root arc is the **FQC-transported** parameter `c₂(t*)` of the height
shift (MNS Theorem 3.2), not the seed parameter `c_b` — this is by design (the critical Écalle
height is shifted to `0`), and it is the parameter at which the PARIMPL2/GATE2 data are taken in
`Work.MandelFinal.finalInputs_of`. -/
theorem rootArcHeightZero_of
    (hES : Work.SeedExist.ExplicitRootSeed)
    (hfat : ∀ (c z : ℂ) (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c)
      ((Tantibar c)^[5]) z), c ∈ Mandelbar → Work.SeedExist.FatouCritInBasin c z fl.Pg) :
    Work.FinalFix.RootArcHeightZero := by
  obtain ⟨c, hd⟩ := Work.SeedExist.rootParabolicEL_of_explicitSeed hES
    (fun c hc => Work.SeedDyn.dynBottcherHomeo hc) hfat Work.TopJordan.jordanForm
  obtain ⟨d⟩ := hd
  exact rootArcHeightZero_of_rootParabolic d

/-- **The pointed form of the missing input.**  The route above consumes the strong Fatou input only
at *one* place: the seed `S = ExplicitRootSeed.toData hES` and one flower of it.  This is the
strictly weaker named input that a caller may supply instead (it matches
`Work.SeedExist.rootParabolicEL_of_seedData`): a single instance of `FatouCritInBasin` at the
certified seed.  It is stated here for the *general* `RootSeedData`, which makes it reusable. -/
theorem rootArcHeightZero_of_seedData (S : Work.SeedExist.RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c))
    (hbott : Work.ParamRays.IsDynBottcher S.c (Work.ParamRays.dynPhiOf S.c))
    (hfat : Work.SeedExist.FatouCritInBasin S.c S.z₁ (Work.SeedExist.flowerOf S).Pg)
    (hJ : Work.Top.JordanForm) : Work.FinalFix.RootArcHeightZero :=
  rootArcHeightZero_of_rootParabolic
    (Work.SeedExist.rootParabolicEL_of_seedData S hN hbott hfat hJ).some

end Work.MandelFinal
