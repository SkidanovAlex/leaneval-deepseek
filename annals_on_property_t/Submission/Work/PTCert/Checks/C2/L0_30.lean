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

theorem ldl_ok0_119 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [126] acc0_119 = some acc0_120 := by decide +kernel
theorem ldl_ok0_120 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [127] acc0_120 = some acc0_121 := by decide +kernel
theorem ldl_ok0_121 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [128] acc0_121 = some acc0_122 := by decide +kernel
theorem ldl_ok0_122 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [129] acc0_122 = some acc0_123 := by decide +kernel

end Submission.PTCert.C2K
end
