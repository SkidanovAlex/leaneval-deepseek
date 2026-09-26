import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K0
import Submission.Work.PTCert.Data.C2.RWAll
import Submission.Work.PTCert.Data.C2.L0
import Submission.Work.PTCert.Data.C2.A0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem ldl_ok0_19 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [26] acc0_19 = some acc0_20 := by decide +kernel
theorem ldl_ok0_20 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [27] acc0_20 = some acc0_21 := by decide +kernel
theorem ldl_ok0_21 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [28] acc0_21 = some acc0_22 := by decide +kernel
theorem ldl_ok0_22 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [29] acc0_22 = some acc0_23 := by decide +kernel

end Submission.PTCert.C2K
end
