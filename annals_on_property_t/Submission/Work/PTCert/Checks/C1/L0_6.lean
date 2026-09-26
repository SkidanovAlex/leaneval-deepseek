import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K0
import Submission.Work.PTCert.Data.C1.RWAll
import Submission.Work.PTCert.Data.C1.L0
import Submission.Work.PTCert.Data.C1.A0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C1K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D1

theorem ldl_ok0_23 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [30] acc0_23 = some acc0_24 := by decide +kernel
theorem ldl_ok0_24 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [31] acc0_24 = some acc0_25 := by decide +kernel
theorem ldl_ok0_25 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [32] acc0_25 = some acc0_26 := by decide +kernel
theorem ldl_ok0_26 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [33] acc0_26 = some acc0_27 := by decide +kernel

end Submission.PTCert.C1K
end
