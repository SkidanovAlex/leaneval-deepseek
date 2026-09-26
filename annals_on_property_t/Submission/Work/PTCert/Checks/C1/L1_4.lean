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

theorem ldl_ok1_15 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [50,51,52] acc1_15 = some acc1_16 := by decide +kernel
theorem ldl_ok1_16 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [53,54,55] acc1_16 = some acc1_17 := by decide +kernel
theorem ldl_ok1_17 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [56,57,58] acc1_17 = some acc1_18 := by decide +kernel
theorem ldl_ok1_18 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [59,60,61] acc1_18 = some acc1_19 := by decide +kernel

end Submission.PTCert.C1K
end
