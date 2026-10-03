import Mathlib
import Submission.Work.FIArea2.Ccount_smooth_eq_poisson
import Submission.Work.FIArea2.sec9_frequency_sum_bound
import Submission.Work.FIArea2.lemma_7_1
import Submission.Work.FIArea2.SmoothSec6Defs
import Submission.Work.FIArea2.G8Defs

namespace Work.FIArea2

open scoped BigOperators

/-- Peeling a single index off a `tsum`: for a summable `f` and any index `a`,
`Σ' n, f n − f a = Σ' n, if n = a then 0 else f n`. -/
lemma tsum_sub_single (f : ℤ × ℤ → ℂ) (hf : Summable f) (a : ℤ × ℤ) :
    (∑' n, f n) - f a = ∑' n, (if n = a then 0 else f n) := by
  rw [hf.tsum_eq_add_tsum_ite a]; ring

end Work.FIArea2
