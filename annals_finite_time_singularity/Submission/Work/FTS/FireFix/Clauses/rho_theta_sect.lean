import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses

/-- **The `(ρ, θ)` coordinates of the point `ρ' (cos θ' e_r + sin θ' e_z)`.**

Writing `y := ρ' • (cos θ' • e_r x + sin θ' • e_z)` for a point `x` off the axis and a positive
radius `ρ'`, the sector `|θ'| < π/2` has all of its `y`-coordinates nonnegative: the radial part
`(y 0, y 1, 0) = ρ' cos θ' • e_r x` carries the factor `ρ' cos θ'` and the axial part is
`ρ' sin θ'`.  Hence `radSq y = (ρ' cos θ')²`, `axial y = ρ' sin θ'` and consequently
`ρ(y) = ρ'`, while `radial y = √(radSq y) = ρ' cos θ' > 0` (here `cos θ' > 0` is exactly the
sector hypothesis), so `θ(y) = arctan (ρ' sin θ' / (ρ' cos θ')) = arctan (tan θ') = θ'`. -/
theorem rho_theta_sect (x : EuclideanSpace ℝ (Fin 3)) (hr : 0 < Work.Cyl.radial x)
    {ρ' θ' : ℝ} (hρ' : 0 < ρ') (hθ' : |θ'| < Real.pi / 2) :
    Work.Cyl.rho (ρ' • (Real.cos θ' • Work.Cyl.eR x + Real.sin θ' • Work.Cyl.eZ)) = ρ' ∧
      Work.Cyl.theta (ρ' • (Real.cos θ' • Work.Cyl.eR x + Real.sin θ' • Work.Cyl.eZ)) = θ' := by
  have hth : -(Real.pi / 2) < θ' ∧ θ' < Real.pi / 2 := abs_lt.mp hθ'
  have hcos : 0 < Real.cos θ' := Real.cos_pos_of_mem_Ioo ⟨hth.1, hth.2⟩
  set y := ρ' • (Real.cos θ' • Work.Cyl.eR x + Real.sin θ' • Work.Cyl.eZ) with hy
  have hy0 : y 0 = ρ' * Real.cos θ' * (x 0 / Work.Cyl.radial x) := by
    rw [hy]; simp [Work.Cyl.eR, div_eq_inv_mul]; ring
  have hy1 : y 1 = ρ' * Real.cos θ' * (x 1 / Work.Cyl.radial x) := by
    rw [hy]; simp [Work.Cyl.eR, div_eq_inv_mul]; ring
  have hy2 : y 2 = ρ' * Real.sin θ' := by
    rw [hy]; simp [Work.Cyl.eR]
  have hradSq : Work.Cyl.radSq y = (ρ' * Real.cos θ') ^ 2 := by
    rw [Work.Cyl.radSq, hy0, hy1]
    field_simp
    rw [Work.Cyl.radial_sq, show Work.Cyl.radSq x = x 0 ^ 2 + x 1 ^ 2 from rfl]
  have hradial : Work.Cyl.radial y = ρ' * Real.cos θ' := by
    rw [Work.Cyl.radial, hradSq, Real.sqrt_sq_eq_abs]
    exact abs_of_pos (mul_pos hρ' hcos)
  have hsinCos : (ρ' * Real.cos θ') ^ 2 + (ρ' * Real.sin θ') ^ 2 = ρ' ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ']
  constructor
  · rw [Work.Cyl.rho, Work.Cyl.axial_eq, hradSq, hy2, hsinCos, Real.sqrt_sq_eq_abs]
    exact abs_of_pos hρ'
  · rw [Work.Cyl.theta, Work.Cyl.axial_eq, hy2, hradial]
    have hdiv : ρ' * Real.sin θ' / (ρ' * Real.cos θ') = Real.sin θ' / Real.cos θ' := by
      field_simp
    rw [hdiv, ← Real.tan_eq_sin_div_cos, Real.arctan_tan hth.1 hth.2]

end Work.FTS.FireFix.Clauses
