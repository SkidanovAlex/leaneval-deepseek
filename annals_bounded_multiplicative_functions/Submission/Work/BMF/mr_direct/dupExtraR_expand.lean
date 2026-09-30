import Mathlib
import Submission.Work.BMF.mr_direct.dupExtraR_defs
import Submission.Work.BMF.mr_direct.dupExtra_expand

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- Unfolding of `dupExtraR` as a single sum over the index set `pSetDR`: the product of the
prime sum and the remainder sum is expanded, and `p^{-s} · m^{-s} = (p·m)^{-s}` is used. -/
theorem dupExtraR_expand (b c : ℕ → ℂ) (K P Q A B : ℝ) (t : ℝ) :
    Work.BMF.mrDirect.dupExtraR b c K P Q A B t =
      ∑ x ∈ Work.BMF.mr_direct.pSetDR K P Q A B,
        Work.BMF.mr_direct.gamD b c P Q x *
          ((Work.BMF.mr_direct.nnD x : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) := by
  classical
  simp only [Work.BMF.mrDirect.dupExtraR, Work.BMF.mr_direct.pSetDR,
    Work.BMF.mr_direct.pairSetD, Finset.sum_sigma,
    Work.BMF.mr_direct.gamD, Work.BMF.mr_direct.nnD,
    Work.BMF.mrDirect.remPolyR_eq_winIdxR, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro m hm
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

end Work.BMF.mr_direct
