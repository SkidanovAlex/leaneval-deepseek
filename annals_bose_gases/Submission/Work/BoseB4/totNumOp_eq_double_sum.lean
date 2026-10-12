import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.DGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- **The total number operator as a double sum with the identity kernel.**

`totNumOp m = ∑_i a_i† a_i` (`Work.BoseB4.DGamma`) is the diagonal part
`∑_{l,l'} δ_{ll'} a_l† a_{l'}` of the mode index pairs: writing the Kronecker
symbol `δ_{ll'} = if l = l' then (1 : ℝ) else 0` as a scalar, the inner sum over
`l'` collapses to its `l' = l` term (all other scalars vanish). This is the form
in which the second quantisation of a general one-particle operator
`dGamma T = ∑_{ij} T_{ij} a_i† a_j` specialises to `T = 1`
(`dGamma_one`): the identity matrix has entries `δ_{ll'}` in the mode basis. -/
theorem totNumOp_eq_double_sum (m : ℕ) :
    Work.BoseB4.totNumOp m = ∑ l : Fin m, ∑ l' : Fin m,
      (if l = l' then (1 : ℝ) else 0) • ((Work.BoseB4.cre m l).comp (Work.BoseB4.ann m l')) := by
  simp only [totNumOp, modeNumOp]
  refine Finset.sum_congr rfl fun l _ => ?_
  -- the scalar `δ_{ll'}` can be pushed into the summand as a genuine `if`
  have hterm : ∀ l' : Fin m, (if l = l' then (1:ℝ) else 0) • (cre m l).comp (ann m l')
      = if l = l' then (cre m l).comp (ann m l') else 0 := by
    intro l'; by_cases h : l = l' <;> simp [h]
  rw [Finset.sum_congr rfl fun l' _ => hterm l', Finset.sum_ite_eq]
  simp

end Work.BoseB4
