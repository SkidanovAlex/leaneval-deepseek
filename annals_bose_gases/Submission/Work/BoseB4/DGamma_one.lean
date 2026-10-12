import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Submission.Work.BoseB4.DGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.DGamma_one` — `dGamma 1 = N`, the total number operator

The second quantisation of the identity one-particle operator is the total number
operator.

Indeed `dGamma T = ∑_{i,j} (T e_j)_i · a_i† a_j` and `(1 e_j)_i = (e_j)_i = δ_{ij}`,
so all the cross terms `i ≠ j` vanish and the double sum collapses to the diagonal
`∑_i a_i† a_i`.

This is the `T = 1` row of FS `lem:2ndQuand`: the kinetic energy
`∑_k τ(k) a_k†a_k` with all weights equal to one is the number of excited modes
(`n₊` in node B7's language).
-/

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

theorem DGamma_one (m : ℕ) :
    Work.BoseB4.dGamma m (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) = Work.BoseB4.totNumOp m := by
  -- `dGamma T = ∑ᵢ ∑ⱼ (T eⱼ)ᵢ • aᵢ†aⱼ`; for `T = 1` the coefficient `(eⱼ)ᵢ` is `δᵢⱼ`.
  simp only [Work.BoseB4.dGamma, Work.BoseB4.totNumOp, Work.BoseB4.modeNumOp, Work.BoseB4.evec]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- the inner sum over `j` collapses to the single term `j = i`
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Work.BoseB4
