/-
Work of the Neukirch–Uchida team: the reconstruction of the field isomorphism `σ` (CoNF XII §12.2).

Import this module to get every definition and theorem of
`Submission/Work/ReconstructField/`; the main theorem is
`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius`, in
`Submission.NK.ReconstructField.Main`.
-/
import Submission.NK.ReconstructField.Basic
import Submission.NK.ReconstructField.Lift
import Submission.NK.ReconstructField.exists_ringEquiv_mapsBase_of_ringEquiv
import Submission.NK.ReconstructField.exists_twist_of_mapsBase
import Submission.NK.ReconstructField.splitsCompletely_levelMap_iff
import Submission.NK.ReconstructField.Bauer
import Submission.NK.ReconstructField.Input
import Submission.NK.ReconstructField.Equivalence
import Submission.NK.ReconstructField.reconstructionInput_refl
import Submission.NK.ReconstructField.ncard_primesOver_levelMap
import Submission.NK.ReconstructField.finrank_eq_of_localCorrespondence
import Submission.NK.ReconstructField.primeTransport_eq_primeMap_of_realizesPlaceCorrespondence
import Submission.NK.ReconstructField.splitsCompletely_rat_iff_of_localCorrespondence
import Submission.NK.ReconstructField.exists_ringEquiv_of_isGalois_of_splitsCompletely_iff
import Submission.NK.ReconstructField.GaloisCase
import Submission.NK.ReconstructField.Targets
import Submission.NK.ReconstructField.Rigidity
import Submission.NK.ReconstructField.Weak
import Submission.NK.ReconstructField.Main
import Submission.NK.ReconstructField.Repair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
