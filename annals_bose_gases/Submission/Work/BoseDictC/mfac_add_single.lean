import Mathlib.Algebra.Group.Finsupp
import Mathlib.Data.Real.Basic
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseDictC

theorem mfac_add_single {m : ℕ} (β : Fin m →₀ ℕ) (l : Fin m) :
    Work.BoseB4.mfac (β + Finsupp.single l 1) = ((β l : ℝ) + 1) * Work.BoseB4.mfac β := by
  have h := Work.BoseB4.mfac_add_e l β
  rw [Work.BoseB4.e] at h
  exact h

end Work.BoseDictC
