import ChallengeDeps
import Submission.Helpers
import Submission.Chen.Reduction
import Submission.Work.ChenPlan.Assembly.chen_rate_of_inputs
import Submission.Work.ChenPlan.LinearSieve.linear_sieve_v6
import Submission.Work.ChenPlan.H1.h1_of_sieve_three
import Submission.Work.ChenPlan.H2.h2_of_sieve_three
import Submission.Work.ChenPlan.H3.h3_of_sieve_three

open LeanEval.NumberTheory.ChenTheorem
open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Submission

theorem chen_theorem :
    {p : ℕ | p.Prime ∧ HasAtMostTwoPrimeFactors (p + 2)}.Infinite :=
  Submission.chen_infinite_of_rate_lower_bound
    (Work.ChenPlan.Assembly.chen_rate_of_inputs
      (Work.ChenPlan.H1.h1_of_sieve_three Work.ChenPlan.LinearSieve.linear_sieve_v6.2)
      (Work.ChenPlan.H2.h2_of_sieve_three Work.ChenPlan.LinearSieve.linear_sieve_v6.1)
      (Work.ChenPlan.H3.h3_of_sieve_three Work.ChenPlan.LinearSieve.linear_sieve_v6.1))

end Submission
