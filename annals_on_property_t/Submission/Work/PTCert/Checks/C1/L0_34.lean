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

theorem ldl_ok0_135 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [149,150,151,152] acc0_135 = some acc0_136 := by decide +kernel
theorem ldl_ok0_136 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [153,154,155,156,157,158,159,160] acc0_136 = some acc0_137 := by decide +kernel

end Submission.PTCert.C1K
end
