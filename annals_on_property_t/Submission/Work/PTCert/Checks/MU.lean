import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls
import Submission.Work.PTCert.Data.R1
import Submission.Work.PTCert.Data.R2
import Submission.Work.PTCert.Data.R3
import Submission.Work.PTCert.Data.R4
import Submission.Work.PTCert.Data.R5
import Submission.Work.PTCert.Data.R6
import Submission.Work.PTCert.Data.R7
import Submission.Work.PTCert.Data.R8
import Submission.Work.PTCert.Data.R9
import Submission.Work.PTCert.Data.R10
import Submission.Work.PTCert.Data.R11
import Submission.Work.PTCert.Data.R12
import Submission.Work.PTCert.Data.R13
import Submission.Work.PTCert.Data.R14
import Submission.Work.PTCert.Data.R15
import Submission.Work.PTCert.Data.R16
import Submission.Work.PTCert.Data.R17

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem mult_ok0 : multOK multT 0 1 cntL = true := by decide +kernel
theorem mult_ok1 : multOK multT 1 80 sizes1 = true := by decide +kernel
theorem mult_ok2 : multOK multT 2 80 sizes2 = true := by decide +kernel
theorem mult_ok3 : multOK multT 3 40 sizes3 = true := by decide +kernel
theorem mult_ok4 : multOK multT 4 40 sizes4 = true := by decide +kernel
theorem mult_ok5 : multOK multT 5 480 sizes5 = true := by decide +kernel
theorem mult_ok6 : multOK multT 6 240 sizes6 = true := by decide +kernel
theorem mult_ok7 : multOK multT 7 80 sizes7 = true := by decide +kernel
theorem mult_ok8 : multOK multT 8 80 sizes8 = true := by decide +kernel
theorem mult_ok9 : multOK multT 9 80 sizes9 = true := by decide +kernel
theorem mult_ok10 : multOK multT 10 80 sizes10 = true := by decide +kernel
theorem mult_ok11 : multOK multT 11 480 sizes11 = true := by decide +kernel
theorem mult_ok12 : multOK multT 12 480 sizes12 = true := by decide +kernel
theorem mult_ok13 : multOK multT 13 480 sizes13 = true := by decide +kernel
theorem mult_ok14 : multOK multT 14 480 sizes14 = true := by decide +kernel
theorem mult_ok15 : multOK multT 15 240 sizes15 = true := by decide +kernel
theorem mult_ok16 : multOK multT 16 240 sizes16 = true := by decide +kernel
theorem mult_ok17 : multOK multT 17 960 sizes17 = true := by decide +kernel

end Submission.PTCert.C
end
