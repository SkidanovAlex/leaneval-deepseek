import Mathlib
import Submission.Work.FIArea4.PairSumCommon

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The local variance is the sum of the squared class sums.**  Unwinding
`Work.FIPlan.Evar` (11.7) — a sum over the residue classes `a < d` of the squared modulus of
`Σ_{r̄s ≡ a (d)} α_{rs} (r/d')` — and grouping each class sum as a sum over the pair set
`EvarCls R S d a`, the two presentations are the same double sum: the product set
`EvarR R d ×ˢ [1,2S]` filtered by the congruence `s ≡ r a (mod d)` is, by
`sum_product_filter`, the nested sum over `r ∈ EvarR R d` and `s ∈ [1,2S]` with that
congruence.  (Note `d = 0` is harmless: `range 0 = ∅` makes both sides `0`.) -/
theorem Evar_eq_sum_clsSum (R S d : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Evar R S d α = ∑ a ∈ Finset.range d, Complex.normSq (clsSum R S d α a) := by
  rw [Work.FIPlan.Evar]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  simp only [clsSum, jw]
  rw [EvarCls, EvarR]
  exact Eq.symm (sum_product_filter _ _ _ _)

end

end Work.FIArea4
