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

theorem ldl_ok1_11 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [38,39,40] acc1_11 = some acc1_12 := by decide +kernel
theorem ldl_ok1_12 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [41,42,43] acc1_12 = some acc1_13 := by decide +kernel
theorem ldl_ok1_13 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [44,45,46] acc1_13 = some acc1_14 := by decide +kernel
theorem ldl_ok1_14 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [47,48,49] acc1_14 = some acc1_15 := by decide +kernel

end Submission.PTCert.C1K
end
