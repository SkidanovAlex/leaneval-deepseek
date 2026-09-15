import ChallengeDeps
import Submission.Vinogradov.Elementary
import Submission.Vinogradov.ShortMoments
import Submission.Vinogradov.Quadratic
import Submission.Vinogradov.Discretisation

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

set_option autoImplicit false

namespace Submission.Vinogradov

noncomputable section
open Classical

/-! ## The deep core

For `3 ≤ k` and `k + 1 ≤ s` the estimate is the full main conjecture for the
Vinogradov system of degree `k` (Wooley's nested efficient congruencing,
arXiv:1708.01220; Bourgain–Demeter–Guth decoupling, Ann. Math. 184 (2016);
see `ROADMAP.lean`).  By the reductions of `Decoupling.lean`,
`DecouplingThm12.lean` and `Discretisation.lean` this regime — and indeed
every regime — follows from the single analytic inequality `bdg_thm_ntmain`
(BDG's ℓ²-decoupling theorem for the moment curve, Theorem 1.2): the
discretisation bound `bdg_Jsep` (BDG Cor. 4.2), the inclusion `J ≤ Jsep` and
the asymptotics assembly are all proven (`bdg_Jsep_core`, `J_le_Jsep`,
`vmvt_of_Jsep_bound`), so

    core_vinogradov = vmvt_of_bdg s k ε hε,

i.e. the whole deep core is formally reduced to `bdg_thm_ntmain` (BDG Thm 1.2),
the ℓ²-decoupling theorem for the moment curve; the intervening steps BDG
Cor. 4.2 (`bdg_Jsep_core`) and BDG Thm 4.1 (`bdg_discrete_restriction`, whose
critical case is `bdg_critical`) are proved, see `ROADMAP.lean`. -/
theorem core_vinogradov (s k : ℕ) (hk3 : 3 ≤ k) (hs : k + 1 ≤ s)
    (ε : ℝ) (hε : 0 < ε) : VMVT s k ε hε := by
  exact vmvt_of_bdg s k (by omega) (by omega) ε hε

end
end Submission.Vinogradov
