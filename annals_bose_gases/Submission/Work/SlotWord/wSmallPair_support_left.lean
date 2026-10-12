import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SlotWord

/-- **Left support of the localised two-body kernel.**

`wSmallPair M L d u ρ x y = χ_{B(u)}(x)·W(x−y)·χ_{B(u)}(y)` is a product whose *first*
factor is the small-box cutoff `χ_{B(u)}(x) = chiSmallB M L d u x` at the left variable.
If `x ∉ B(u) = dlBox L d u` then that cutoff vanishes
(`chiSmallB_support_mem_dlBox` in contrapositive form), and hence the whole product is
zero. -/
theorem wSmallPair_support_left {M : ℕ} (hM : 1 ≤ M) {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ Submission.BoseGases.dlBox L d u)
    (y : EuclideanSpace ℝ (Fin 3)) : Submission.BoseGases.wSmallPair M L d u ρ x y = 0 := by
  have hx0 : Submission.BoseGases.chiSmallB M L d u x = 0 := by
    by_contra hne
    exact hx (chiSmallB_support_mem_dlBox hM hL hd hne)
  simp only [Submission.BoseGases.wSmallPair, hx0, zero_mul]

end Work.SlotWord
