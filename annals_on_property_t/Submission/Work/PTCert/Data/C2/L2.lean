import Submission.Work.PTCert.KernelCert
import Submission.Work.PTCert.Data.C2.L2_0
import Submission.Work.PTCert.Data.C2.L2_1
import Submission.Work.PTCert.Data.C2.L2_2
import Submission.Work.PTCert.Data.C2.L2_3

set_option maxRecDepth 100000
noncomputable section
namespace Submission.PTCert.D2
open Submission.PTCert

def Cs2 : List (List (List ℤ)) := [C2_0, C2_1, C2_2, C2_3]
def Ws2 : List (List ℤ) := [W2_0, W2_1, W2_2, W2_3]

end Submission.PTCert.D2
end
