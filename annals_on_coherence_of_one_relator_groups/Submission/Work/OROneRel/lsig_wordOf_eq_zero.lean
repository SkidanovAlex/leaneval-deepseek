import Mathlib
import Submission.Work.OROneRel.wgtMMDefs

namespace Work.OROneRel

universe u

/-- `lsig` of the reduced word of `u` computes the exponent sum of `u`: if `cohom c u = 1`
(i.e. the total `c`-weight of `u` vanishes) then `lsig c (wordOf u) = 0`. -/
theorem lsig_wordOf_eq_zero {α : Type u} [DecidableEq α] (c : α → ℤ) (u : FreeGroup α)
    (hcu : Work.OROneRel.cohom c u = 1) : Work.OROneRel.lsig c (Work.OROneRel.wordOf u) = 0 := by
  have h1 : cohom c (FreeGroup.mk (wordOf u)) = Multiplicative.ofAdd (lsig c (wordOf u)) :=
    cohom_mk c (wordOf u)
  rw [mk_wordOf] at h1
  have h2 : Multiplicative.ofAdd (lsig c (wordOf u)) = (1 : Multiplicative ℤ) := by
    rw [← h1]; exact hcu
  exact Multiplicative.ofAdd.injective (by simpa using h2)

end Work.OROneRel
