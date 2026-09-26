import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K1
import Submission.Work.PTCert.Data.C1.RWAll
import Submission.Work.PTCert.Data.C1.L1
import Submission.Work.PTCert.Data.C1.A1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C1K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D1

theorem ldl_ok1_23 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [84,85,86,87] acc1_23 = some acc1_24 := by decide +kernel

end Submission.PTCert.C1K
end
