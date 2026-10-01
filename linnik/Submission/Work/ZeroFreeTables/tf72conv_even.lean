/-
# `tf72conv` is even

The convolution `tf72conv lam t = ∫ s, g lam s * g lam (t - s)` of the even function
`tf72g` with itself is even: substituting `s ↦ -s` (the Lebesgue measure on `ℝ` is
invariant under negation) and using `tf72g_even` twice gives the claim.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

namespace Work.ZeroFreeTables

theorem tf72conv_even (lam : ℝ) (hlam : 0 < lam) :
    ∀ t : ℝ, Work.ZeroFreeTables.tf72conv lam (-t) = Work.ZeroFreeTables.tf72conv lam t := by
  intro t
  unfold Work.ZeroFreeTables.tf72conv
  -- Change variable `s ↦ -s` in the defining integral (Lebesgue measure is negation-invariant).
  rw [← MeasureTheory.integral_neg_eq_self
    (fun s : ℝ => Work.ZeroFreeTables.tf72g lam s * Work.ZeroFreeTables.tf72g lam (-t - s))
    MeasureTheory.volume]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show Work.ZeroFreeTables.tf72g lam (-s) * Work.ZeroFreeTables.tf72g lam (-t - -s)
      = Work.ZeroFreeTables.tf72g lam s * Work.ZeroFreeTables.tf72g lam (t - s)
  rw [show -t - -s = -(t - s) by ring, Work.ZeroFreeTables.tf72g_even lam s,
      Work.ZeroFreeTables.tf72g_even lam (t - s)]

end Work.ZeroFreeTables
