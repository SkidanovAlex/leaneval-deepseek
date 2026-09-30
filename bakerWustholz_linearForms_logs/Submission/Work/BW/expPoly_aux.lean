import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

namespace Work.BW

noncomputable section

/-- The finite-difference operator on complex polynomials based at `w`:
`Op w Q = C w * taylor 1 Q - Q`, i.e. `(Op w Q)(x) = w · Q(x + 1) - Q(x)`.
Iterating `Op (z i / z i₀)` kills the `i₀`-component of an exponential-polynomial identity
(the base `1` component drops degree) and leaves the other bases unchanged. -/
def Op (w : ℂ) (Q : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.C w * Polynomial.taylor (1 : ℂ) Q - Q

@[simp] lemma Op_zero (w : ℂ) : Op w 0 = 0 := by simp [Op]

/-- Evaluation of the finite-difference operator. -/
lemma Op_eval (w : ℂ) (Q : Polynomial ℂ) (x : ℂ) :
    (Op w Q).eval x = w * Q.eval (x + 1) - Q.eval x := by
  simp only [Op, eval_sub, eval_mul, eval_C, taylor_apply, eval_comp, eval_add, eval_X]

/-- One finite-difference step applied simultaneously to a family of polynomials: the
`wᵢ`-weighted sums of the `Op`-images equal the difference of the shifted and unshifted sums. -/
lemma sum_step {ι : Type*} (s : Finset ι) (w : ι → ℂ) (R : ι → Polynomial ℂ) (t : ℕ) :
    ∑ i ∈ s, (w i) ^ t * (Op (w i) (R i)).eval (t : ℂ)
      = ∑ i ∈ s, (w i) ^ (t + 1) * (R i).eval ((t + 1 : ℕ) : ℂ)
        - ∑ i ∈ s, (w i) ^ t * (R i).eval (t : ℂ) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Op_eval, pow_succ]
  push_cast
  ring

end

end Work.BW
