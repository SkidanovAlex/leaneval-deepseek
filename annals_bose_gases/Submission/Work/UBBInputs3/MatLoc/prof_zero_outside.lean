import Mathlib.Analysis.Real.Sqrt
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.prof_zero_outside`

The normalised triangle profile `prof p s = tri p s / √(triMass p)` vanishes for
`|s| > p`: the triangle `tri p s = max 0 (p + 1 - |s|)` has support `[-p,p]`, so
`(p : ℤ) < |s|` forces `tri p s = 0` and hence `prof p s = 0`.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

/-- The triangle profile vanishes where `(p : ℤ) < |s|`. -/
lemma tri_eq_zero_of_lt_abs (p : ℕ) (s : ℤ) (h : (p : ℤ) < |s|) :
    Work.UBBInputs3.tri p s = 0 := by
  rw [Work.UBBInputs3.tri, max_eq_left]
  have h' : (p : ℝ) + 1 ≤ |(s : ℝ)| := by
    have h1 : (((p : ℤ) + 1 : ℤ) : ℝ) ≤ ((|s| : ℤ) : ℝ) := by
      exact_mod_cast (by omega : (p : ℤ) + 1 ≤ |s|)
    simpa [Int.cast_abs] using h1
  linarith

theorem prof_zero_outside (p : ℕ) (s : ℤ) (h : (p : ℤ) < |s|) : Work.UBBInputs3.prof p s = 0 := by
  rw [Work.UBBInputs3.prof, tri_eq_zero_of_lt_abs p s h, zero_div]

end Work.UBBInputs3.MatLoc
