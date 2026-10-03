import Mathlib
import Submission.Work.L62.bl_geom_basic

/-!
# `Work.L62.tau0_piExp_image_isOpen`

The composite `w ↦ τ₀ (π w) = -e^{-2πiw}` is an open map (it is a composition of the open maps
`w ↦ (2πi) w`, `y ↦ -y`, `exp` and `z ↦ -z`; the first is a homeomorphism because `2πi ≠ 0`, and
`Complex.exp` is an open map).  Consequently `τ₀ '' (π '' S)` is open for every open `S`, since
`τ₀ '' (π '' S) = (τ₀ ∘ π) '' S`.

The point of the composite formulation is that the junk value `τ₀ 0 = 0` is never used:
`τ₀ ∘ π = -e^{-2πi·}` is entire, so no separate discussion of `0` is needed.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

private theorem isOpenMap_tau0_piExp : IsOpenMap (fun w : ℂ => tau0 (piExp w)) := by
  have hfun : (fun w : ℂ => tau0 (piExp w))
      = fun w : ℂ => -(Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))) :=
    funext fun w => tau0_piExp w
  rw [hfun]
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  have h1 : IsOpenMap (fun w : ℂ => 2 * (Real.pi : ℂ) * Complex.I * w) :=
    (Homeomorph.mulLeft₀ (2 * (Real.pi : ℂ) * Complex.I) hc).isOpenMap
  have h2 : IsOpenMap (fun y : ℂ => -y) := (Homeomorph.neg ℂ).isOpenMap
  have h3 : IsOpenMap Complex.exp := Complex.isOpenMap_exp
  have h4 : IsOpenMap (fun z : ℂ => -z) := (Homeomorph.neg ℂ).isOpenMap
  exact ((h4.comp h3).comp h2).comp h1

theorem tau0_piExp_image_isOpen {S : Set ℂ} (hS : IsOpen S) :
    IsOpen (MandelDim.tau0 '' (MandelDim.piExp '' S)) := by
  rw [Set.image_image]
  exact isOpenMap_tau0_piExp S hS

end

end Work.L62
