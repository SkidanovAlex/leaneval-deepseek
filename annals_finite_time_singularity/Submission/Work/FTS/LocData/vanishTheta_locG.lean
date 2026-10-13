import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.LocData.vanishTheta_locG` — the angular vanishing of the localised perturbation

The perturbation `g = locG α L β h = -zfar L F_* + β h` of the route is a `VanishTheta`
function: it vanishes on both angular boundaries `θ = 0` and `θ = π/2` of the quadrant.

The reason is that *both* terms do: `F_* = α (Γ(θ)/c(α)) 2z/(1+z)²` has the angular factor
`Γ(θ) = (sin θ cos²θ)^{α/3}`, which vanishes at `θ = 0` (because `sin 0 = 0`) and at
`θ = π/2` (because `cos (π/2) = 0`), the exponent `α/3 > 0` being strictly positive; and `h`
vanishes there by hypothesis.  Note that the vanishing of `F_*` on the boundary is used only
through the two *pointwise* facts `Fstar_theta_zero` and `Fstar_theta_pi_half` below — no
regularity, no integrability, and in particular no hypothesis on `L`, is involved.

(The hypotheses `hα1 : α ≤ 1` of the statement are not needed here; they are part of the
uniform interface of the chapter.)
-/

set_option linter.unusedVariables false

namespace Work.FTS.LocData

/-- `F_*(z,0) = 0`: the angular factor `Γ(0) = (sin 0 · cos²0)^{α/3} = 0` because
`sin 0 = 0` and the exponent `α/3` is nonzero. -/
theorem Fstar_theta_zero (α : ℝ) (hα : 0 < α) (z : ℝ) : Work.Construction.Fstar α z 0 = 0 := by
  rw [Work.Construction.Fstar, Work.Spaces.Gam,
    show Real.sin 0 * Real.cos 0 ^ 2 = 0 by simp,
    Real.zero_rpow (by positivity : α / 3 ≠ 0), zero_div]
  ring

/-- `F_*(z,π/2) = 0`: the angular factor `Γ(π/2) = (sin(π/2) · cos²(π/2))^{α/3} = 0` because
`cos (π/2) = 0`. -/
theorem Fstar_theta_pi_half (α : ℝ) (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z (Real.pi / 2) = 0 := by
  rw [Work.Construction.Fstar, Work.Spaces.Gam,
    show Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2 = 0 by
      simp [Real.cos_pi_div_two],
    Real.zero_rpow (by positivity : α / 3 ≠ 0), zero_div]
  ring

/-- **The angular vanishing of the localised perturbation.**  If `h` vanishes at `θ = 0` and
`θ = π/2`, so does `locG α L β h = F_*·χ(·/L) + β h - F_*`: both `F_*·χ(·/L)` and `F_*` vanish
on the boundary and `β · h` does by hypothesis. -/
theorem vanishTheta_locG (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ}
    (hh : ∀ z : ℝ, h z 0 = 0 ∧ h z (Real.pi / 2) = 0) :
    Work.Spaces.VanishTheta (locG α L β h) := by
  constructor
  · intro z
    rw [locG_apply, locData_apply, Fstar_theta_zero α hα z, (hh z).1]
    ring
  · intro z
    rw [locG_apply, locData_apply, Fstar_theta_pi_half α hα z, (hh z).2]
    ring

end Work.FTS.LocData
