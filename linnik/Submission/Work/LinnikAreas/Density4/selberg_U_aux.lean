import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
import Submission.Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound

namespace Work.LinnikAreas.Density4

open scoped BigOperators

noncomputable section

/-- `A(t) = Σ_{m ≤ ⌊t⌋} μ(m)/m`: the partial sums of `μ(m)/m`, as a function of the real
variable `t` (constant on the unit intervals).  This is the function whose integral against
`dt/t` reproduces `selU`. -/
noncomputable def muRecip (t : ℝ) : ℝ := Commons.NumberTheory.Moebius.muRecipSum ⌊t⌋₊

/-- `L = ∫_1^∞ A(t) dt/t`, the limit of `selU`. -/
noncomputable def selULimit : ℝ := ∫ t in Set.Ioi 1, muRecip t / t

end

end Work.LinnikAreas.Density4
