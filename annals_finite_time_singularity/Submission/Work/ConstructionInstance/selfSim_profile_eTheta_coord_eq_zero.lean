import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- The `j`-th coordinate of the `i`-th standard basis vector of `ℝ³` is `0` when `j ≠ i`. -/
lemma basisVec_apply_of_ne {i j : Fin 3} (h : j ≠ i) : (Work.Cyl.basisVec i) j = 0 := by
  simp only [Work.Cyl.basisVec, FiniteTimeSingularity.e, WithLp.ofLp_toLp, Pi.single_apply]
  exact ite_eq_right h

/-- Shifting along `basisVec i` with `i ≠ 2` does not change the axial coordinate. -/
lemma axial_add_smul_basisVec_of_ne_two {i : Fin 3} (hi : i ≠ 2) (x : R3) (t : ℝ) :
    Work.Cyl.axial (x + t • Work.Cyl.basisVec i) = Work.Cyl.axial x := by
  rw [Work.Cyl.axial, Work.Cyl.axial]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    basisVec_apply_of_ne (Ne.symm hi), mul_zero, add_zero]

/-- Shifting along `basisVec i` with `i ≠ 2` keeps a point in the plane `x₃ = 0`: the polar
angle `θ` of the shifted point vanishes. -/
lemma theta_add_smul_basisVec_eq_zero_of_axial_eq_zero {i : Fin 3} (hi : i ≠ 2)
    {x : R3} (hx : Work.Cyl.axial x = 0) (t : ℝ) :
    Work.Cyl.theta (x + t • Work.Cyl.basisVec i) = 0 := by
  rw [Work.Cyl.theta, axial_add_smul_basisVec_of_ne_two hi x t, hx, zero_div, Real.arctan_zero]

/-- **The profile times the `i`-th coordinate of `e_θ` vanishes** for the point `x + t • eᵢ`
whenever `x` lies on the axis (`radial x = 0`) or in the plane `x₃ = 0` (`axial x = 0`).

The two vanishing mechanisms are complementary: if `x` is on the axis (`r = 0`) then the
`i`-th coordinate of `e_θ` vanishes at the shifted point (both because `e_θ` has no axial
component and because the relevant in-plane coordinate of the shifted point is inherited
from `x`); if `x` lies in the plane `x₃ = 0` and `i ≠ 2` the shift preserves `x₃ = 0`, so the
polar angle `θ` vanishes and the profile — which is odd in `θ` and vanishes at `θ = 0` by
`hg0` — is zero. -/
theorem selfSim_profile_eTheta_coord_eq_zero {p c : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hg0 : ∀ z : ℝ, g z 0 = 0) {x : Work.ConstructionInstance.R3}
    (hx : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0) (i : Fin 3) (t : ℝ) :
    Work.ConstructionInstance.profile p g (Work.Cyl.rho (x + t • Work.Cyl.basisVec i) ^ p / c)
        (Work.Cyl.theta (x + t • Work.Cyl.basisVec i))
      * (Work.Cyl.eTheta (x + t • Work.Cyl.basisVec i)) i = 0 := by
  rcases hx with hx | hx
  · -- `radial x = 0`: the `i`-th coordinate of `e_θ` at the shifted point vanishes.
    have hx0 : x 0 = 0 := ((Work.Cyl.radial_eq_zero_iff x).mp hx).1
    have hx1 : x 1 = 0 := ((Work.Cyl.radial_eq_zero_iff x).mp hx).2
    have h : (Work.Cyl.eTheta (x + t • Work.Cyl.basisVec i)) i = 0 := by
      fin_cases i <;>
        simp [Work.Cyl.eTheta, Work.Cyl.angularVec, Work.Cyl.basisVec, FiniteTimeSingularity.e,
          hx0, hx1]
    rw [h, mul_zero]
  · -- `axial x = 0`: if `i ≠ 2` the shift preserves `x₃ = 0`; if `i = 2` the axial component
    -- of `e_θ` vanishes.
    by_cases hi : i = 2
    · subst hi
      rw [Work.Cyl.eTheta_apply_two, mul_zero]
    · rw [theta_add_smul_basisVec_eq_zero_of_axial_eq_zero hi hx t,
        Work.ConstructionInstance.profile_zero hp hg0, zero_mul]

end Work.ConstructionInstance
