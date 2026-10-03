import Mathlib
import Submission.Work.Pert.Ksub2.Setup

namespace Work.Pert.Ksub2

open MandelDim

/-- The algebra identity behind the limit model: writing `t = τ₀ w = -1/w`, if
`f₀ t = t + t² hF t` then `τ₀ (f₀ t) = w + hF t / (1 + t hF t)`.  Since `F0f f₀ w = τ₀ (f₀ (τ₀ w))`
by definition, this is the statement. -/
theorem F0f_eq_model {f₀ hF : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0)
    (hfe : f₀ (MandelDim.tau0 w) = MandelDim.tau0 w + MandelDim.tau0 w ^ 2 * hF (MandelDim.tau0 w))
    (hden : 1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0) :
    Work.Pert.F0f f₀ w
      = w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) := by
  rw [Work.Pert.F0f]
  set t := MandelDim.tau0 w with ht
  have hwt : w * t = -1 := by
    rw [ht, MandelDim.tau0]
    field_simp [hw]
  have ht0 : t ≠ 0 := by
    intro h; rw [h, mul_zero] at hwt
    exact absurd hwt (by norm_num)
  have hA : 1 + t * hF t ≠ 0 := hden
  have htinv : -1 / t = w := by
    rw [div_eq_iff ht0]
    rw [hwt]
  have hfe' : f₀ t = t * (1 + t * hF t) := by rw [hfe]; ring
  have htau : MandelDim.tau0 (t * (1 + t * hF t)) = -1 / (t * (1 + t * hF t)) := by
    simp [MandelDim.tau0]
  have step1 : -1 / (t * (1 + t * hF t)) = (-1 / t) / (1 + t * hF t) := by
    rw [div_div]
  have step2 : w + hF t / (1 + t * hF t) = (w * (1 + t * hF t) + hF t) / (1 + t * hF t) := by
    rw [add_div, mul_div_cancel_right₀ _ hA]
  have h3 : w * (1 + t * hF t) + hF t = w := by
    linear_combination (hF t) * hwt
  have h4 : w / (1 + t * hF t) = (w * (1 + t * hF t) + hF t) / (1 + t * hF t) := by
    refine mul_right_cancel₀ hA ?_
    rw [div_mul_cancel₀ w hA, div_mul_cancel₀ _ hA, h3]
  rw [hfe', htau, step1, htinv, step2]
  exact h4

end Work.Pert.Ksub2
