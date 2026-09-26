import ChallengeDeps
import Submission.Helpers
import Submission.PropertyT
import Submission.FreeGroupAut
import Submission.Work.PTCert.Certs

open OnPropertyT

set_option autoImplicit false

namespace Submission

theorem theorem_1 (n : ℕ) (hn : n ≥ 6) : PropertyT (MulAut (FreeGroup (Fin n))) :=
  Submission.RouteB.Edge.theorem_1_of_certificates Submission.PTCert.saut5DeltaCert
    Submission.PTCert.saut5Adj2OpCert n hn

end Submission
