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

theorem ldl_ok0_55 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [62] acc0_55 = some acc0_56 := by decide +kernel
theorem ldl_ok0_56 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [63] acc0_56 = some acc0_57 := by decide +kernel
theorem ldl_ok0_57 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [64] acc0_57 = some acc0_58 := by decide +kernel
theorem ldl_ok0_58 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [65] acc0_58 = some acc0_59 := by decide +kernel

end Submission.PTCert.C2K
end
