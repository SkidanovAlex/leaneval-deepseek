import Submission.Work.RHContract.A.psiTail_ge_of_RH
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.A.regionIII_margin_positive
import Submission.Work.RHContract.A.RegionIIIFromMargin

/-!
# `Work.RHContract.A.robin_ca_regionIII` — Region III (`ξ ≥ 10^8`)

Under `RH`, Robin's inequality at `N_ε` whenever `ξ(ε) ≥ 10^8`.  The proof combines

* `A.ca_margin_lower` (Lemma M of ROUTE_LEAD §2.3),
* `A.psiTail_ge_of_RH` (A1),
* `A.regionIII_margin_positive` (the explicit arithmetic inequality of ROUTE_LEAD §2.4),

through the assembly `Work.RHContract.robin_ca_regionIII_of_marginPositive`.

This replaces an earlier proof of the same statement through
`A.R3.caDelta_le` / `A.caDelta_numeric`; that route needed the numeric `Δ`-sum bound
`Σ_{2≤k≤K}(caU((1.23kξ)^{1/k}) − caL(ξ^{1/k})) ≤ 2.5√ξ`, which is being re-proved separately
(see `NOTES.md`) and is not needed for the challenge theorem.
-/

open scoped ArithmeticFunction.sigma

namespace Work.RHContract.A

theorem robin_ca_regionIII (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε)
    (hlo : (10 : ℝ) ^ 8 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) :=
  Work.RHContract.robin_ca_regionIII_of_marginPositive h ε hε hlo
    (Work.RHContract.A.regionIII_margin_positive h ε hε hlo)

end Work.RHContract.A
