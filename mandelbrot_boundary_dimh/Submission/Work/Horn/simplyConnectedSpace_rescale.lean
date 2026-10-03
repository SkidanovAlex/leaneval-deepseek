import Mathlib
import Submission.Work.Interfaces.Parabolic

open scoped Pointwise

namespace Work.Horn

/-- Multiplication by a nonzero complex number is a homeomorphism of `ℂ`, and the image of a
set under it is simply connected exactly when the set is. -/
theorem simplyConnectedSpace_rescale {B : Set ℂ} {s : ℂ} (hs : s ≠ 0)
    (h : SimplyConnectedSpace B) : SimplyConnectedSpace ((fun ζ : ℂ => s * ζ) '' B) := by
  have h' : IsSimplyConnected ((fun ζ : ℂ => s * ζ) '' B) := by
    have himg : (fun ζ : ℂ => s * ζ) '' B = s • B := by
      ext x
      simp [Set.mem_smul_set]
    rw [himg, isSimplyConnected_smul_set₀_iff hs]
    exact h
  exact h'

end Work.Horn
