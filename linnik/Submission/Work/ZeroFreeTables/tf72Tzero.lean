import Mathlib
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.tf72Fc_zero_re
import Submission.Work.ZeroFreeTables.testFn72_defs

/-!
# ZeroFreeTables/tf72Tzero

The two tabulated values of HB Lemma 7.2's test function at the origin,
`tf72T_F_zero` (`F 0 = 8/9`) and `tf72T_f_zero` (`f 0 = 16λ/15`).

They used to live in `tf72G.lean` (together with the closed form `G72` of `F`); they are split off
here so that consumers who only need these two values do not import the real-valued `G72`, which
clashes with the complex-valued `G72` of the off-axis chapter `OffAxis/G72Defs.lean`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- `F 0 = 8/9` for the test function of HB Lemma 7.2 (HB's tabulated value). -/
theorem tf72T_F_zero (lam : ℝ) (hlam : 0 < lam) : (tf72T lam hlam).F 0 = 8/9 := by
  show (tf72Fc lam ((0:ℝ) : ℂ)).re = 8/9
  rw [show ((0:ℝ) : ℂ) = 0 from by norm_num]
  exact tf72Fc_zero_re lam hlam

/-- `f 0 = 16λ/15` for the test function of HB Lemma 7.2. -/
theorem tf72T_f_zero (lam : ℝ) (hlam : 0 < lam) : (tf72T lam hlam).f 0 = 16*lam/15 :=
  tf72f_at_zero lam hlam

end Work.ZeroFreeTables
