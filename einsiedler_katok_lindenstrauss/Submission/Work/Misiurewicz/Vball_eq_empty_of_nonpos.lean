import Mathlib
import Submission.Work.EKLComp.Misiurewicz.Defs

namespace Work.Misiurewicz

open Work.EKLContract

/-! ## The displacement neighbourhoods `V r` for `r ≤ 0` are empty

`V r = {g | ∀ i j, |g i j - 1 i j| < r}` contains no element for `r ≤ 0`, because
`|g 0 0 - 1| ≥ 0 ≥ r`.  Consequently every `V`-ball `Vball r z = (fun u => u • z) '' V r`
is empty as well. This is the degenerate case of the neighbourhoods used in the
Misiurewicz construction. -/

/-- `V r` is empty for `r ≤ 0`: the identity entry `g 0 0` would have to satisfy
`|g 0 0 - 1| < r ≤ 0`, which is impossible. -/
theorem V_eq_empty_of_nonpos {r : ℝ} (hr : r ≤ 0) : V r = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨g, hg⟩
  have h := hg 0 0
  simp only [Matrix.one_apply_eq] at h
  have := abs_nonneg (g 0 0 - (1 : ℝ))
  linarith

/-- The translate `V r • z` is empty for `r ≤ 0`. -/
theorem Vball_eq_empty_of_nonpos {r : ℝ} (hr : r ≤ 0) (z : Work.EKLContract.X3) :
    Work.EKLComp.Vball r z = ∅ := by
  rw [Work.EKLComp.Vball, V_eq_empty_of_nonpos hr, Set.image_empty]

end Work.Misiurewicz
