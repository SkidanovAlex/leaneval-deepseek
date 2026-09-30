import Mathlib
import Submission.Work.BMF.mr_direct.dupExtra_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open scoped BigOperators

/-- Unfolding of `dupExtra` as a single sum over the index set `pSetD`: the product of the
prime sum and the remainder sum is expanded, and `p^{-s} · m^{-s} = (p·m)^{-s}` is used. -/
theorem dupExtra_expand (b c : ℕ → ℂ) (K P Q X : ℝ) (t : ℝ) :
    Work.BMF.mrDirect.dupExtra b c K P Q X t =
      ∑ x ∈ Work.BMF.mrDirect.pSetD K P Q X,
        Work.BMF.mr_direct.gamD b c P Q x *
          ((Work.BMF.mr_direct.nnD x : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) := by
  classical
  simp only [Work.BMF.mrDirect.dupExtra, Work.BMF.mrDirect.pSetD, Finset.sum_sigma,
    Work.BMF.mr_direct.gamD, Work.BMF.mr_direct.nnD, Work.BMF.mrDirect.remPoly_eq,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro m hm
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

end Work.BMF.mr_direct
