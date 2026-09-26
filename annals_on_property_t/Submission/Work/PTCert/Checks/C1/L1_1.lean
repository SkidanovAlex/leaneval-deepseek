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

theorem ldl_ok1_3 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [14,15,16] acc1_3 = some acc1_4 := by decide +kernel
theorem ldl_ok1_4 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [17,18,19] acc1_4 = some acc1_5 := by decide +kernel
theorem ldl_ok1_5 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [20,21,22] acc1_5 = some acc1_6 := by decide +kernel
theorem ldl_ok1_6 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [23,24,25] acc1_6 = some acc1_7 := by decide +kernel

end Submission.PTCert.C1K
end
