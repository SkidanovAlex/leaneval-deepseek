import Submission.Work.PTCert.KernelCert
import Submission.Work.PTCert.Data.C2.L3_0
import Submission.Work.PTCert.Data.C2.L3_1
import Submission.Work.PTCert.Data.C2.L3_2
import Submission.Work.PTCert.Data.C2.L3_3

set_option maxRecDepth 100000
noncomputable section
namespace Submission.PTCert.D2
open Submission.PTCert

def Cs3 : List (List (List ℤ)) := [C3_0, C3_1, C3_2, C3_3]
def Ws3 : List (List ℤ) := [W3_0, W3_1, W3_2, W3_3]

end Submission.PTCert.D2
end
