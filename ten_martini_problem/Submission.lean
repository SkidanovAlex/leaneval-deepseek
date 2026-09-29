import ChallengeDeps
import Submission.Helpers
import Submission.Work.TMContract.Glue
import Submission.Work.TMC14Core.Contract
import Submission.Work.TMComp.prove_UniqErg
import Submission.Work.TMComp.prove_OpBasics
import Submission.Work.TMComp.prove_Perfect
import Submission.Work.TMComp.prove_Duality
import Submission.Work.TMComp.prove_LEBasics
import Submission.Work.TMComp.prove_RotBasics
import Submission.Work.TMComp.prove_IDSSpectrum
import Submission.Work.TMComp.prove_BJ
import Submission.Work.TMComp.prove_Kotani
import Submission.Work.TMComp.prove_mAnalytic
import Submission.Work.TMComp.prove_RealCartan
import Submission.Work.TMComp.prove_Reducibility
import Submission.Work.TMComp.prove_Puig
import Submission.Work.TMComp.prove_FictLip
import Submission.Work.TMComp.prove_Schnol
import Submission.Work.TMComp.prove_Loc
import Submission.Work.TMComp.prove_LocCantor

open LeanEval.Analysis.TenMartini
open Set

namespace Submission

theorem ten_martini_problem (α coupling θ : ℝ)
    (hα : Irrational α) (hcoupling : coupling ≠ 0) :
    ∃ H : EllTwo →L[ℂ] EllTwo,
      IsAlmostMathieuOperator α coupling θ H ∧
        (spectrum ℂ H).Nonempty ∧
        IsCompact (spectrum ℂ H) ∧
        Perfect (spectrum ℂ H) ∧
        IsTotallyDisconnected (spectrum ℂ H) :=
  Work.TMContract.ten_martini_problem_of_components
    Work.TMComp.prove_UniqErg Work.TMComp.prove_OpBasics Work.TMComp.prove_Perfect
    Work.TMComp.prove_Duality Work.TMComp.prove_LEBasics Work.TMComp.prove_RotBasics
    Work.TMComp.prove_IDSSpectrum Work.TMComp.prove_BJ Work.TMComp.prove_Kotani
    Work.TMComp.prove_mAnalytic Work.TMComp.prove_RealCartan Work.TMComp.prove_Reducibility
    Work.TMComp.prove_Puig Work.TMComp.prove_FictLip
    (Work.TMC14Core.p_gapBound_contract Work.TMComp.prove_LEBasics Work.TMComp.prove_RotBasics
      Work.TMComp.prove_IDSSpectrum Work.TMComp.prove_BJ)
    Work.TMComp.prove_Schnol Work.TMComp.prove_Loc Work.TMComp.prove_LocCantor
    α coupling θ hα hcoupling

end Submission
