import ChallengeDeps
import Submission.Helpers
import Submission.Work.EKLContract.Glue
import Submission.Work.EKLComp.prove_Dioph
import Submission.Work.EKLComp.prove_BoxDim
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLComp.prove_EntropyBasics
import Submission.Work.EKLComp.prove_Misiurewicz
import Submission.Work.EKLComp.prove_ErgodicMax
import Submission.Work.EKLComp.prove_EntropyLeaf
import Submission.Work.EKLComp.prove_RelCross
import Submission.Work.EKLComp.prove_Commutator
import Submission.Work.EKLComp.prove_LowEntropyCore
import Submission.Work.EKLComp.prove_NonExc
import Submission.Work.EKLComp.prove_Endgame

open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

namespace Submission

theorem einsiedler_katok_lindenstrauss :
    dimH {(α, β) : ℝ × ℝ | Filter.atTop.liminf
      (fun n : ℕ ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) > 0} = 0 :=
  Work.EKLContract.ekl_challenge Work.EKLComp.prove_Dioph Work.EKLComp.prove_BoxDim
    Work.EKLComp.prove_X3 Work.EKLComp.prove_EntropyBasics Work.EKLComp.prove_Misiurewicz
    Work.EKLComp.prove_ErgodicMax Work.EKLComp.prove_EntropyLeaf Work.EKLComp.prove_RelCross
    Work.EKLComp.prove_Commutator Work.EKLComp.prove_LowEntropyCore Work.EKLComp.prove_NonExc
    Work.EKLComp.prove_Endgame

end Submission
