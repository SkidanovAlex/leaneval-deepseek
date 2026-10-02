import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Reed.Prob.freeze_exp

/-!
# The slice identity for frozen product measures

Under the product measure in which the coordinate `g` is frozen at the point mass `c`, the
expectation of `Z` equals that of `Z ∘ (update · g c)`: the measure is supported on the fibre
`{f | f g = c}`, on which `Function.update f g c = f`, and off it the weight is `0`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed.Prob

/-- In the product measure with the coordinate `g` frozen at `c`, the expectation of `Z`
equals that of `Z ∘ (update · g c)`. -/
theorem freeze_exp_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (ν : ∀ i, FinProb (Ω i)) (g : ι) (c : Ω g)
    (Z : (∀ i, Ω i) → ℝ) :
    (FinProb.pi (FinProb.freeze ν g c)).exp Z
      = (FinProb.pi (FinProb.freeze ν g c)).exp (fun f => Z (Function.update f g c)) := by
  rw [FinProb.exp, FinProb.exp]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : f g = c
  · rw [show Function.update f g c = f from Function.update_eq_self_iff.mpr h.symm]
  · rw [FinProb.pi_freeze_wt, FinProb.point_wt_of_ne h]
    ring

end Work.Deep.Reed.Prob
