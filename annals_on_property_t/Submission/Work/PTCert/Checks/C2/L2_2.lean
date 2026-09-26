import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K2
import Submission.Work.PTCert.Data.C2.RWAll
import Submission.Work.PTCert.Data.C2.L2
import Submission.Work.PTCert.Data.C2.A2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem ldl_ok2_7 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 3 ks2 ys2 Cs2 Ws2 [44,45,46,47,48,49,50,51,52,53,54,55,56,57,58] acc2_7 = some acc2_8 := by decide +kernel

end Submission.PTCert.C2K
end
