import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SlotWord

/-- **Left support of the localised one-body kernel.**

`wSmall1Pair h M L d u x y = χ_{B(u)}(x)·W(x−y)·χ_{B(u)}(y)` is the product of the
sliding cutoff at `x`, a factor depending only on `x − y`, and the sliding cutoff at `y`.
If `x ∉ B(u) = dlBox L d u` then the cutoff at `x` vanishes — by the contrapositive of
`chiSmallB_support_mem_dlBox` the support of `chiSmallB M L d u` is contained in
`dlBox L d u` — and hence the whole product is `0`, for every `y`.

This is the "outside the box the kernel is strictly localised" half of the sliding-kernel
support API. -/
theorem wSmall1Pair_support_left {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ} (hM : 1 ≤ M)
    {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ Submission.BoseGases.dlBox L d u)
    (y : EuclideanSpace ℝ (Fin 3)) : Submission.BoseGases.wSmall1Pair h M L d u x y = 0 := by
  have hchi : Submission.BoseGases.chiSmallB M L d u x = 0 := by
    by_contra hne
    exact hx (chiSmallB_support_mem_dlBox hM hL hd hne)
  simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hchi, zero_mul]

end Work.SlotWord
