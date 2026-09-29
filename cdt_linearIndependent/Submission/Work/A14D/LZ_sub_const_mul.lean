import Mathlib
import Submission.Work.A14D.setup

/-!
# `LZ` is linear: `Z(f - c·g) = Zf - c·Zg`

The Zagier operator `LZ f = PZ·f'' + PZ'·f' + RZ·f` (`Submission.Work.A14.defs`) is linear in `f`.
Since `LZ` is expressed through the *total* Mathlib derivative `deriv`, the outer (second)
derivative requires the first derivative to be differentiable at the point.  For complex
differentiable functions on an open set this is free: such a function is analytic
(`DifferentiableOn.deriv`), so its derivative is again complex differentiable.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

/-- Linearity of the Zagier operator `LZ` in the direction `f - c * g`.  Complex differentiability
on the open set `Ω` is enough: by analyticity the second derivatives exist there. -/
theorem LZ_sub_const_mul {Ω : Set ℂ} (hΩ : IsOpen Ω) {f g : ℂ → ℂ} (c : ℂ)
    (hf : DifferentiableOn ℂ f Ω) (hg : DifferentiableOn ℂ g Ω) {z : ℂ} (hz : z ∈ Ω) :
    Work.A14D.LZ (fun w => f w - c * g w) z = Work.A14D.LZ f z - c * Work.A14D.LZ g z := by
  have hz' : Ω ∈ 𝓝 z := hΩ.mem_nhds hz
  -- first derivatives
  have hdf : DifferentiableAt ℂ f z := hf.differentiableAt hz'
  have hdg : DifferentiableAt ℂ g z := hg.differentiableAt hz'
  have hdcg : DifferentiableAt ℂ (fun w => c * g w) z := hdg.const_mul c
  -- second derivatives: analyticity on the open set gives differentiability of `deriv`
  have hddf : DifferentiableAt ℂ (deriv f) z := (hf.deriv hΩ).differentiableAt hz'
  have hddg : DifferentiableAt ℂ (deriv g) z := (hg.deriv hΩ).differentiableAt hz'
  -- the first derivative of `f - c * g` is `deriv f - c * deriv g` near `z`
  have h1 : deriv (fun w => f w - c * g w) =ᶠ[𝓝 z]
      (fun w => deriv f w - c * deriv g w) := by
    filter_upwards [hz'] with w hw
    have hwf : DifferentiableAt ℂ f w := hf.differentiableAt (hΩ.mem_nhds hw)
    have hwg : DifferentiableAt ℂ g w := hg.differentiableAt (hΩ.mem_nhds hw)
    rw [show (fun w : ℂ => f w - c * g w) = (f - fun w : ℂ => c * g w) from by
      funext w; rfl]
    rw [deriv_sub hwf (hwg.const_mul c), deriv_const_mul c hwg]
  -- hence the second derivatives agree
  have h2 : deriv (deriv (fun w => f w - c * g w)) z
      = deriv (fun w => deriv f w - c * deriv g w) z := h1.deriv_eq
  have h3 : deriv (fun w => deriv f w - c * deriv g w) z
      = deriv (deriv f) z - c * deriv (deriv g) z := by
    rw [show (fun w : ℂ => deriv f w - c * deriv g w)
          = (deriv f - fun w : ℂ => c * deriv g w) from by funext w; rfl]
    rw [deriv_sub hddf (hddg.const_mul c), deriv_const_mul c hddg]
  have h4 : deriv (fun w => f w - c * g w) z = deriv f z - c * deriv g z := by
    rw [show (fun w : ℂ => f w - c * g w) = (f - fun w : ℂ => c * g w) from by funext w; rfl]
    rw [deriv_sub hdf hdcg, deriv_const_mul c hdg]
  simp only [Work.A14D.LZ]
  rw [h2, h3, h4]
  ring

end Work.A14D
