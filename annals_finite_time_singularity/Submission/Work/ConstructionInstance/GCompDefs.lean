/-
# `Work.ConstructionInstance.GCompDefs`

Auxiliary definitions for the Hölder regularity of the perturbation composite

  `ĝ x = g (ρ x ^ (3α)) (|θ x|)`

of `Work.ConstructionInstance.holder_gComp`.

The only non-trivial object here is the **corrected angle**

  `psi x = arccos (radial x / rho x) ∈ [0, π/2]`,

where `radial x = r(x)` is the distance of `x` to the symmetry axis and `rho x = ρ(x) = ‖x‖`.
Off the axis it coincides with `|θ x|`, and on the axis it equals `π/2` (whereas Lean's
`theta = arctan (x₃ / r)` takes the junk value `0` there); since the perturbation `g` vanishes
both at `θ = 0` and at `θ = π/2`, the composite `g (ρ^{3α}) (|θ|)` is unchanged if `|θ|` is
replaced by `psi` everywhere.  The virtue of `psi` is that it is *continuous* (and locally
Lipschitz with constant `1/ρ`), so no special case on the axis is needed.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set

namespace Work.ConstructionInstance

/-- **The corrected polar angle** `psi x = arccos (r x / ρ x)`, where `r = Cyl.radial` is the
distance to the symmetry axis and `ρ = Cyl.rho = ‖x‖`.  This lies in `[0, π/2]` and equals
`|Cyl.theta x|` whenever `r x > 0`. -/
def psi (x : R3) : ℝ := Real.arccos (Work.Cyl.radial x / Work.Cyl.rho x)

/-- `rho x = rhoP (radial x) (axial x)`: the `ℝ³` radius is the planar radius of the
`(r, x₃)`-coordinates. -/
theorem rho_eq_rhoP (x : R3) :
    Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
  rw [Work.Cyl.rho, Work.Cyl.rhoP]
  congr 1
  rw [Work.Cyl.radial_sq]

/-- The corrected angle lies in `[0, π/2]`. -/
theorem psi_mem_Iθ (x : R3) : psi x ∈ Work.Spaces.Iθ := by
  refine ⟨Real.arccos_nonneg _, ?_⟩
  rw [psi, Real.arccos_le_pi_div_two]
  exact div_nonneg (Work.Cyl.radial_nonneg x) (Work.Cyl.rho_nonneg x)

/-- `cos ψ = r / ρ`. -/
theorem cos_psi (x : R3) : Real.cos (psi x) = Work.Cyl.radial x / Work.Cyl.rho x := by
  rw [psi]
  exact Real.cos_arccos (by
      have h := div_nonneg (Work.Cyl.radial_nonneg x) (Work.Cyl.rho_nonneg x)
      linarith)
    (div_le_one_of_le₀ (Work.Cyl.radial_le_rho x) (Work.Cyl.rho_nonneg x))

/-- `sin ψ = |x₃| / ρ`. -/
theorem sin_psi {x : R3} (h : 0 < Work.Cyl.rho x) :
    Real.sin (psi x) = |x 2| / Work.Cyl.rho x := by
  rw [psi, Real.sin_arccos]
  have hρ : 0 < Work.Cyl.rho x := h
  have hkey : 1 - (Work.Cyl.radial x / Work.Cyl.rho x) ^ 2
      = ((x 2) / Work.Cyl.rho x) ^ 2 := by
    have h1 : Work.Cyl.radial x ^ 2 = Work.Cyl.radSq x := Work.Cyl.radial_sq x
    have h2 : Work.Cyl.rho x ^ 2 = Work.Cyl.radSq x + Work.Cyl.axial x ^ 2 :=
      Work.Cyl.rho_sq x
    have h3 : Work.Cyl.axial x = x 2 := rfl
    field_simp
    rw [h3] at h2
    linarith
  rw [hkey, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hρ]

/-- `cos θ = r / ρ` off the axis. -/
theorem cos_theta_eq {x : R3} (h : 0 < Work.Cyl.radial x) :
    Real.cos (Work.Cyl.theta x) = Work.Cyl.radial x / Work.Cyl.rho x := by
  have h1 : Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl
  rw [h1, Work.Cyl.cos_thetaP h, rho_eq_rhoP]

/-- Off the axis the corrected angle is the absolute value of `theta`. -/
theorem psi_eq_abs_theta {x : R3} (h : 0 < Work.Cyl.radial x) :
    psi x = |Work.Cyl.theta x| := by
  have hθ : |Work.Cyl.theta x| ≤ Real.pi := by
    have h1 : -(Real.pi / 2) < Work.Cyl.theta x := Real.neg_pi_div_two_lt_arctan _
    have h2 : Work.Cyl.theta x < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    rw [abs_le]
    constructor <;> linarith [Real.pi_pos]
  rw [psi, ← Real.arccos_cos (abs_nonneg _) hθ, Real.cos_abs, cos_theta_eq h]

end Work.ConstructionInstance
