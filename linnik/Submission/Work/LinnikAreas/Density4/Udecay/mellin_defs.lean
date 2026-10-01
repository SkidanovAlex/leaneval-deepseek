import Submission.Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound
import Submission.Work.LinnikAreas.Density4.Udecay.recip_bound

/-!
# Bridge module for the Mellin/Abel series of `μ(n)/n`

Re-exports the definitions and the exponential-decay bound of the partial sums
`muRecipSum m = Σ_{n ≤ m} μ(n)/n` (from `Submission.Commons.NumberTheory.Moebius`)
together with the real-variable decay bound `recip_bound` for `muRecip t = muRecipSum ⌊t⌋₊`.
-/
