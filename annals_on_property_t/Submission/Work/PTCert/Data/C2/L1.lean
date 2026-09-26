import Submission.Work.PTCert.KernelCert
import Submission.Work.PTCert.Data.C2.L1_0
import Submission.Work.PTCert.Data.C2.L1_1
import Submission.Work.PTCert.Data.C2.L1_2
import Submission.Work.PTCert.Data.C2.L1_3

set_option maxRecDepth 100000
noncomputable section
namespace Submission.PTCert.D2
open Submission.PTCert

def Cs1 : List (List (List ℤ)) := [C1_0, C1_1, C1_2, C1_3]
def Ws1 : List (List ℤ) := [W1_0, W1_1, W1_2, W1_3]

end Submission.PTCert.D2
end
