import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls
import Submission.Work.PTCert.Data.C1.Res

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C1K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D1

theorem ressym_ok : resSymOK resT iclT (List.range 7229) = true := by decide +kernel
theorem resbound_ok : resBoundOK resT (List.range 7229) resBound = true := by decide +kernel

end Submission.PTCert.C1K
end
