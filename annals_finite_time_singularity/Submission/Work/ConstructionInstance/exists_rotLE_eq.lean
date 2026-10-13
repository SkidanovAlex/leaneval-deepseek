import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.AxiNoSwirlSymm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- Every point off the symmetry axis is the rotation by some angle of the meridian point
`(r, 0, x₃)` of the same radius `r = radial x` and height `x₃ = axial x`.

Indeed `rotLE φ !₂[r,0,z] = !₂[r cos φ, r sin φ, z]`, so the assertion is that
`(x 0, x 1) = r·(cos φ, sin φ)` for some `φ`, which holds with `φ` the argument of the complex
number `(x 0 + i x 1)/r` since that number has modulus `1` as `r = √(x 0² + x 1²) > 0`. -/
theorem exists_rotLE_eq (x : Work.ConstructionInstance.R3)
    (hr : 0 < Work.Cyl.radial x) :
    ∃ φ : ℝ, Work.ConstructionInstance.rotLE φ
      !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] = x := by
  have hradSq_pos : 0 < Work.Cyl.radSq x := by
    rw [Work.Cyl.radial, Real.sqrt_pos] at hr
    exact hr
  -- `radial x ^ 2` is the squared distance of `x` to the axis, `x 0 ^ 2 + x 1 ^ 2`
  have h3 : Work.Cyl.radial x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [Work.Cyl.radial, Real.sq_sqrt (le_of_lt hradSq_pos), Work.Cyl.radSq]
  have hpos : 0 < x 0 ^ 2 + x 1 ^ 2 := by rw [← h3]; positivity
  -- the normalised pair `(x 0 / r, x 1 / r)` lies on the unit circle
  have hsq : (x 0 / Work.Cyl.radial x) ^ 2 + (x 1 / Work.Cyl.radial x) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, h3, div_self (ne_of_gt hpos)]
  obtain ⟨φ, hc, hs⟩ := exists_cos_sin hsq
  refine ⟨φ, ?_⟩
  have hx0 : x 0 = Real.cos φ * Work.Cyl.radial x := by rw [hc]; field_simp
  have hx1 : x 1 = Real.sin φ * Work.Cyl.radial x := by rw [hs]; field_simp
  ext i
  fin_cases i
  · simp [rotCoord, hx0]
  · simp [rotCoord, hx1]
  · simp [rotCoord, Work.Cyl.axial]

end Work.ConstructionInstance
