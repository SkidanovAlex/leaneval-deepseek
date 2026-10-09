-- Re-exports of the `Submission.NeukirchUchida` API, so that lemmas delegated into
-- `Submission/Work/` can be stated in its vocabulary (`MapsBase`, `conj`, `conjHom`, ...).
import Submission.NeukirchUchida.Conjugation
import Submission.NeukirchUchida.FieldTransport
import Submission.NeukirchUchida.GaloisIso
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.NeukirchUchida.Local.Transitivity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
