import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Thom.subsingleton_relComplex_euclidean_punctured
import Submission.Work.Thom.Relocate.HonestFMV
import Submission.Work.Thom.SuspensionStep
import Submission.Work.Thom.modelSphereBundleStep
import Submission.Work.Thom.Glue
import Submission.Work.Thom.ModelThomA

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- `Work.Thom.nonempty_thomClass_trivial_euclidean` re-proved in the island of
`Submission/Work/TangentClasses/` and `Submission/Work/Thom/Interface.lean` (avoiding the
`Submission.Work.Cohomology.dualZ` and `Submission.Work.Cohomology.prod_sphere_aux` islands).
Available: `Work.Thom.nonempty_thomClass_trivial_line` (`Submission/Work/Thom/LineThomClass.lean`,
whose `prod_sphere_aux`-free replacement `Submission/Work/Thom/disjointCoverA.lean` may also be
used); `Work.Thom.ATools` (the transfer tools `cupMap_transfer_iffA` / `_fwdA` / `_bwdA`,
`bijective_relCohMap_of_homeomorphA`); `Work.Thom.EuclCleanInfra.bijective_relCohMap_of_homotopyEquiv`
and `EuclCleanInfra.isIso_homologyMap_relComplexMap` in
`Submission/Work/Thom/subsingleton_relComplex_euclidean_punctured.lean`;
`Work.Thom.suspensionStep_bijective`; `Work.Thom.modelSphereBundleStep`;
`Work.Thom.Relocate.HonestFMV` (honest Mayer--Vietoris injectivity).  The clean copies of
`Work.Thom.bijective_relCohMap_spherePunctured`, `Work.Thom.bijective_relCohMap_discFull` and
`Work.Thom.capRelCohIso` (whose group-`B` proofs use the `dualZ` island; the last one uses
`Work.Cohomology.Endgame.relComplexMapExcision`, so in this island an excision statement has to be
derived from the honest relative Mayer--Vietoris long exact sequence instead) should be added as
auxiliary files in this directory. -/
theorem thomClassTrivialEuclideanA (n : ℕ) (B : Type) [TopologicalSpace B] (hn : 1 ≤ n) :
    Nonempty (Work.Thom.ThomClass
      (Work.TangentClasses.RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) PUnit) n) :=
  CleanA.modelThom_to_thomClass n PUnit (CleanA.modelThom_all B PUnit hn)

end Work.Thom
