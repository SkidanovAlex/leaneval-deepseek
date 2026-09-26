import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K4
import Submission.Work.PTCert.Data.C2.RWAll
import Submission.Work.PTCert.Data.C2.L4
import Submission.Work.PTCert.Data.C2.A4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem ldldata_ok4 : ldlDataOK Cs4 Ws4 6 = true := by decide +kernel
theorem ldl_ok4_0 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 15 ks4 ys4 Cs4 Ws4 [0,1,2,3,4,5] acc4_0 = some acc4_1 := by decide +kernel

end Submission.PTCert.C2K
end
