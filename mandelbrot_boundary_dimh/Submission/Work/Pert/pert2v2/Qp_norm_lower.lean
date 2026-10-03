import Mathlib
import Submission.Work.Pert.Setup

namespace Work.Pert.pert2v2

open Complex

/-- The defining clause of `Qreg` coming from the **lower** vertex `b₁ = Ξ` of the upper gate
`Qp Ξ α = Qreg (some Ξ) (some (-Ξ + 1/α))`: it reads `-|Im z| < Re z - Ξ`, equivalently
`Ξ < Re z + |Im z|`.  (The other clause, the one involving `α`, is not used below.) -/
theorem mem_Qp_re_add_abs_im {Ξ : ℝ} {α z : ℂ} (hz : z ∈ Work.Pert.Qp Ξ α) :
    Ξ < z.re + |z.im| := by
  have h1 : -|(z - (Ξ : ℂ)).im| < (z - (Ξ : ℂ)).re := hz.1 (Ξ : ℂ) (by simp)
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.sub_re,
    Complex.ofReal_re] at h1
  linarith

/-- The upper gate `Qp Ξ α` is disjoint from the open disk of radius `Ξ/2` about the origin.
Indeed the `b₁ = Ξ` clause gives `Ξ < Re z + |Im z| ≤ |Re z| + |Im z| ≤ 2‖z‖`. -/
theorem Qp_norm_lower {Ξ : ℝ} (hΞ : 0 < Ξ) {α z : ℂ} (hz : z ∈ Work.Pert.Qp Ξ α) :
    Ξ / 2 ≤ ‖z‖ := by
  have h := mem_Qp_re_add_abs_im hz
  have hre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  linarith

end Work.Pert.pert2v2
