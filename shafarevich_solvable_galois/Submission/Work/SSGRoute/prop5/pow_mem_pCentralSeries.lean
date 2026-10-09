import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.ProP.lowerCentralSeries_le_pCentralSeries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

/-- Iterated powers of an element of the `(k-1)`-st term of the lower central series land in the
`(k+t-1)`-st term of the descending `p`-central series.

Since `γ_{k-1} ≤ P_{k-1}` (`Work.ProP.lowerCentralSeries_le_pCentralSeries`) and the `p`-th power
map sends `P_n` into `P_{n+1}` (`Work.Shrinking.pow_mem_pCentralSeries_succ`), induction on `t`
gives the claim. -/
theorem pow_mem_pCentralSeries (p : ℕ) {P : Type} [Group P] (k t : ℕ) (hk : 1 ≤ k) (x : P)
    (hx : x ∈ (⊤ : Subgroup P).lowerCentralSeries (k - 1)) :
    x ^ (p ^ t) ∈ Work.Shrinking.pCentralSeries p P (k + t - 1) := by
  have hle : x ∈ Work.Shrinking.pCentralSeries p P (k - 1) :=
    Work.ProP.lowerCentralSeries_le_pCentralSeries p P (k - 1) hx
  induction t with
  | zero => simpa using hle
  | succ t ih =>
      have hpow : x ^ (p ^ (t + 1)) = (x ^ (p ^ t)) ^ p := by
        rw [pow_succ, pow_mul]
      rw [hpow]
      have hstep := Work.Shrinking.pow_mem_pCentralSeries_succ p P ih
      have hidx : (k + t - 1) + 1 = k + (t + 1) - 1 := by omega
      rwa [hidx] at hstep

end Work.SSGRoute.prop5
