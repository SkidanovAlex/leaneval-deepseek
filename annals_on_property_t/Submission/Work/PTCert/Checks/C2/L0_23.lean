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

theorem ldl_ok0_91 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [98] acc0_91 = some acc0_92 := by decide +kernel
theorem ldl_ok0_92 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [99] acc0_92 = some acc0_93 := by decide +kernel
theorem ldl_ok0_93 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [100] acc0_93 = some acc0_94 := by decide +kernel
theorem ldl_ok0_94 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [101] acc0_94 = some acc0_95 := by decide +kernel

end Submission.PTCert.C2K
end
