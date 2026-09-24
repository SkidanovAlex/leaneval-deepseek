import Submission.Work.ChenPlan.H3.h3_sieve_three_aux
import Submission.Work.ChenPlan.H3.oddPrime_interval_logDiv

/-!
# Chen's `h3` from the upper linear sieve (2026-09-24 v6 interface)

`LinearSieveUpper` (v6) assumes the four hypotheses `IsLinear`, `IsLinearRange`, `IsLinearLower`,
`IsLinearMertens`.  The first three are supplied for `bSieve` by
`Work.ChenPlan.H3.isLinear_bSieve_all` (proved); the fourth, Richert's `Ω₁ + Ω₂(1,L)` for the
odd-prime density `ν p = 1/(p-1)`, is the interval Mertens estimate

  `|Σ_{w ≤ p < z'} log p/(p-1) − log (z'/w)| ≤ K`,  `2 ≤ w < z'`,

which is the delegated lemma `Work.ChenPlan.H3.oddPrime_interval_logDiv`
(proved from `Commons.NumberTheory.Mertens.sum_log_div_le_log_sharp`).  The whole reduction from
the v6 sieve to `H3Statement` is carried out in
`Submission.Work.ChenPlan.H3.h3_sieve_three_aux`; all that is left here is to discharge the
interval hypothesis.
-/

namespace Work.ChenPlan.H3

/-- Chen's h3 from the linear sieve, against the v6 interface (`IsLinearMertens`). -/
theorem h3_of_sieve_three (hU : Submission.ChenPlan.LinearSieveUpper) : Submission.ChenPlan.H3Statement :=
  h3_of_sieve_three_of_interval hU oddPrime_interval_logDiv

end Work.ChenPlan.H3
