import Mathlib
import Submission.Work.BW.expPoly_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Iterating the finite-difference step `Op` preserves the identity
`∑ᵢ wᵢ^t · Rᵢ(t) = 0`: this is `sum_step` run backwards, since
`∑ᵢ wᵢ^t (Op wᵢ Rᵢ)(t) = A_{t+1}(R) - A_t(R)` with `A_t(R) = ∑ᵢ wᵢ^t Rᵢ(t)`. -/
theorem sum_step_iterate {ι : Type*} (s : Finset ι) (w : ι → ℂ) (Q : ι → Polynomial ℂ)
    (h : ∀ t : ℕ, ∑ i ∈ s, (w i) ^ t * (Q i).eval (t : ℂ) = 0) (k : ℕ) :
    ∀ t : ℕ, ∑ i ∈ s, (w i) ^ t * (((Work.BW.Op (w i))^[k]) (Q i)).eval (t : ℂ) = 0 := by
  induction k with
  | zero =>
    intro t
    simpa using h t
  | succ k ih =>
    intro t
    simp only [Function.iterate_succ_apply']
    rw [sum_step s w (fun i => ((Work.BW.Op (w i))^[k]) (Q i)) t]
    rw [ih (t + 1), ih t]
    ring

end Work.BW
