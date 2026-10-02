/-
# `Work.MandelWire.Deps` — the import closure of the wiring

One-stop import of every area module the MandelWire lemmas mention.  The wiring itself is
`Submission/Work/MandelWire/All.lean`.
-/
import Submission.Work.MandelWire.GATE2n.FinalCaseII
import Submission.Work.FQC.Height
import Submission.Work.FQC.transfer_parabolic
import Submission.Work.FlowerGlue.SameWitness
import Submission.Work.FlowerGlue.Coherence
import Submission.Work.FlowerGlue.PetalInput
import Submission.Work.FQCInputs.HeightShift
import Submission.Work.FQCInputs.simpleTransfer_all
import Submission.Work.MandelFinal.seedCert
import Submission.Work.SeedExist.Wire
import Submission.Work.SeedExist.Setup
import Submission.Work.SeedExist.Flower
import Submission.Work.TripodCert.All
import Submission.Work.ELAssembly.Main
import Submission.Work.ELAssembly.hzero_of_transfer
import Submission.Work.ELAssembly.Inputs
import Submission.Work.ELAssembly.Assembly
import Submission.Work.ELAssembly.B2Postcrit
import Submission.Work.ELNest.All
import Submission.Work.ELRig.All
import Submission.Work.ELTop.All
import Submission.Work.GATE2.toZ1Nest_sides
import Submission.Work.GATE2.RayCylLift_mono
import Submission.Work.NAKANE.All
import Submission.Work.PARIMPL2.All
import Submission.Work.PARIMPL.All
import Submission.Work.Final.All
import Submission.Work.FatouDeg.All
import Submission.Work.SeedFatou.All
import Submission.Work.TopJordan.Jordan
import Submission.Work.ParamRaysCrit.All
import Submission.Work.MandelFinal.Classical
import Submission.Work.FinalFix.Nonreal
import Submission.Work.MandelFinal.Root

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

