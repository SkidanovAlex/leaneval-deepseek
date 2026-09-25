import Submission.Work.RHContract.Areas
import Submission.Work.RHContract.A.robin_ca_regionI
import Submission.Work.RHContract.A.robin_ca_regionII
import Submission.Work.RHContract.A.robin_ca_regionIII

/-!
# `Work.RHContract.Final` — the three areas, and the challenge theorem

* **AREA A** `RobinCAFrom1530` is assembled from the three regions of ROUTE_LEAD §2:
  `A.robin_ca_regionI` (`1530 ≤ ξ < 3·10^4`, certified computation of 386 blocks),
  `A.robin_ca_regionII` (`3·10^4 ≤ ξ < 10^8`, q-certificate),
  `A.robin_ca_regionIII` (`10^8 ≤ ξ`, explicit analysis).
* **AREA B1** `LandauInput` is `B.landau_input` (B2–B7 of ROUTE_LEAD §3.3).
* **AREA B2** `TransferInput` is `transferInput_proved` (Lemma T, ROUTE_LEAD §3.1).

Combining them through the proved contract `Work.RHContract.rh_iff_of_areas'` yields the
challenge statement `RiemannHypothesis ↔ LagariasElementaryCriterion`.
-/

open scoped ArithmeticFunction.sigma

namespace Work.RHContract

noncomputable section

/-- **AREA A, proved.**  `RobinCAFrom1530`, from the three regions. -/
theorem robinCAFrom1530_proved : RobinCAFrom1530 :=
  robinCAFrom1530_of_regions
    (fun ε hε h1 h2 => Work.RHContract.A.robin_ca_regionI ε hε h1 h2)
    (fun hRH ε hε h1 h2 => Work.RHContract.A.robin_ca_regionII hRH ε hε h1 h2)
    (fun hRH ε hε h1 => Work.RHContract.A.robin_ca_regionIII hRH ε hε h1)

/-- **THE CHALLENGE THEOREM**, assembled from the three areas of the replacement contract.

This is the deliverable of `Submission/Work/RHContract`: the statement
`RiemannHypothesis ↔ LagariasElementaryCriterion` proved from
`RobinCAFrom1530` (AREA A), `LandauInput` (AREA B1) and `TransferInput` (AREA B2). -/
theorem riemann_hypothesis_iff_lagarias_elementary_criterion :
    RiemannHypothesis ↔ LeanEval.NumberTheory.LagariasElementaryCriterion :=
  rh_iff_of_areas' robinCAFrom1530_proved landauInput_proved transferInput_proved

end

end Work.RHContract
