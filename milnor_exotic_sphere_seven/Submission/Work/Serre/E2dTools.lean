import Submission.Work.Serre.E2dSets
import Submission.Work.Serre.E2dEngine
import Submission.Work.Serre.E2dFibre
import Submission.Work.Serre.nonempty_homology_iso_of_isZero_relChains
import Submission.Work.Serre.compressRel_slabU
import Submission.Work.Serre.compressRel_slabV
import Submission.Work.Serre.mvStep_pullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The toolbox of the E2(d) computation

A single import that brings together all the ingredients built for the E2(d) induction
(`Work.Serre.SerreE2d`): the vocabulary (`E2dSets`), the engine (`E2dEngine`), the fibre
comparison (`E2dFibre`, `nonempty_homology_iso_of_isZero_relChains`), the compression properties
of the slabs (`compressRel_slabU`, `compressRel_slabV`) and the Mayer–Vietoris step
(`mvStep_pullback`).
-/
