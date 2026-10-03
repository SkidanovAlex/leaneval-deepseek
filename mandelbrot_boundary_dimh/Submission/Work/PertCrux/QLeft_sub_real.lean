import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.Setup

namespace Work.PertCrux

/-- **The sector `QLeft ξ` is closed under subtracting a nonnegative real.**

Using the elementary description `QLeft ξ = {w | 2 * (w + ξ).re < ‖w + ξ‖}`
(`Work.Parab.QLeft_iff`), the point `u := w + ξ` satisfies `2 * u.re < ‖u‖` and we want
`2 * (u - t).re < ‖u - t‖` for `t ≥ 0`.  The reverse triangle inequality
`‖u‖ ≤ ‖u - t‖ + t` gives

`2 * (u - t).re = 2 * u.re - 2t < ‖u‖ - 2t ≤ (‖u - t‖ + t) - 2t = ‖u - t‖ - t ≤ ‖u - t‖`,

which is the claim (this generalises `Work.Parab.QLeft_sub_one_local` from `t = 1`). -/
theorem QLeft_sub_real {ξ : ℝ} {w : ℂ} (hw : w ∈ MandelDim.QLeft ξ) {t : ℝ} (ht : 0 ≤ t) :
    w - (t : ℂ) ∈ MandelDim.QLeft ξ := by
  rw [Work.Parab.QLeft_iff] at hw ⊢
  set u : ℂ := w + (ξ : ℂ) with hu
  have hsplit : (w - (t : ℂ)) + (ξ : ℂ) = u - (t : ℂ) := by rw [hu]; ring
  rw [hsplit]
  have hnorm : ‖u‖ ≤ ‖u - (t : ℂ)‖ + t := by
    have h2 : u = (u - (t : ℂ)) + (t : ℂ) := by ring
    calc ‖u‖ = ‖(u - (t : ℂ)) + (t : ℂ)‖ := congrArg norm h2
      _ ≤ ‖u - (t : ℂ)‖ + ‖(t : ℂ)‖ := norm_add_le _ _
      _ = ‖u - (t : ℂ)‖ + t := by
            simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hre : (u - (t : ℂ)).re = u.re - t := by simp
  rw [hre]
  linarith

end Work.PertCrux
