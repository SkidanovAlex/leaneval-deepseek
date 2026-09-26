import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls
import Submission.Work.PTCert.Data.C2.V
import Submission.Work.PTCert.Data.C2.Res
import Submission.Work.PTCert.Data.C2.Q

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem cs_ok1 : classSumOK valT multT resT (fun p => sv (p8 qT p)) 200 1208925819614629174706176 kl1 tl1 500 = true := by decide +kernel

end Submission.PTCert.C2K
end
