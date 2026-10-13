import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Submission.Work.ConstructionInstance.GCompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Work.Cyl

namespace Work.ConstructionInstance

/-! ## A planar Cauchy–Schwarz inequality

The two-dimensional Cauchy–Schwarz inequality in the elementary form we need below: the scalar
product of the planar parts of two vectors of `ℝ³` is bounded by the product of their planar
radii. -/

/-- **Cauchy–Schwarz in the plane.**  For real `a b c d`,  `a c + b d ≤ √(a²+b²)·√(c²+d²)`.
The proof squares both sides (the right-hand side is nonnegative) and uses
`(a²+b²)(c²+d²) - (ac+bd)² = (ad - bc)² ≥ 0`. -/
theorem real_cauchy2 (a b c d : ℝ) :
    a * c + b * d ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by
  have h1 : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by positivity
  have h2 : (a * c + b * d) ^ 2 ≤ (Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (a * d - b * c)]
  nlinarith [sq_nonneg (a * c + b * d), h1, h2]

/-- **Planar Cauchy–Schwarz on `ℝ³`.**  `x₀y₀ + x₁y₁ ≤ r(x)·r(y)`, where `r = Cyl.radial` is the
planar radius: the horizontal part of `⟪x,y⟫` is at most the product of the horizontal radii. -/
theorem planar_inner_le (x y : R3) : x 0 * y 0 + x 1 * y 1 ≤ radial x * radial y := by
  have h := real_cauchy2 (x 0) (x 1) (y 0) (y 1)
  simpa only [radial, radSq] using h

/-- **The normalized inner product is at most `cos (ψx - ψy)`.**  Splitting
`⟪x,y⟫ = (x₀y₀ + x₁y₁) + x₂y₂` and using planar Cauchy–Schwarz on the first summand and
`x₂y₂ ≤ |x₂||y₂|` on the second,

  `⟪x,y⟫/(ρx·ρy) ≤ r(x)r(y)/(ρxρy) + |x₂||y₂|/(ρxρy) = cos ψx cos ψy + sin ψx sin ψy
                 = cos (ψx - ψy)`,

with `cos_psi`/`sin_psi` of `GCompDefs` converting the coordinates into `cos ψ`/`sin ψ`. -/
theorem inner_div_le_cos_psi_sub (x y : R3) (hx : 0 < rho x) (hy : 0 < rho y) :
    inner ℝ x y / (rho x * rho y) ≤ Real.cos (psi x - psi y) := by
  rw [inner_eq, Real.cos_sub, cos_psi x, cos_psi y, sin_psi hx, sin_psi hy]
  have hp : 0 < rho x * rho y := mul_pos hx hy
  have hplanar := planar_inner_le x y
  have haz : x 2 * y 2 ≤ |x 2| * |y 2| := by
    calc x 2 * y 2 ≤ |x 2 * y 2| := le_abs_self _
      _ = |x 2| * |y 2| := abs_mul _ _
  rw [div_le_iff₀ hp]
  have hR : (radial x / rho x * (radial y / rho y) + |x 2| / rho x * (|y 2| / rho y))
        * (rho x * rho y) = radial x * radial y + |x 2| * |y 2| := by
    field_simp
  rw [hR]
  linarith

/-- **`psi` is dominated by the angle between `x` and `y`.**  With `ψ z = arccos (r z / ρ z)`
(`r = Cyl.radial`, `ρ = Cyl.rho = ‖·‖`) this says `|ψ x - ψ y| ≤ angle x y`, where
`InnerProductGeometry.angle x y = arccos (⟪x,y⟫ / (‖x‖‖y‖))`.

Since both `ψ z` lie in `[0, π/2]`, `cos (ψx - ψy) = cos |ψx - ψy|` with `|ψx - ψy| ≤ π/2 ≤ π`, so
`arccos (cos (ψx - ψy)) = |ψx - ψy|` (`Real.arccos_cos`); the previous lemma gives
`⟪x,y⟫/(ρxρy) ≤ cos (ψx - ψy)`, and `Real.arccos_le_arccos` (which is unconditional in the
Mathlib convention for `Real.arccos`) reverses it. -/
theorem abs_psi_sub_le_angle (x y : Work.ConstructionInstance.R3)
    (hx : 0 < Work.Cyl.rho x) (hy : 0 < Work.Cyl.rho y) :
    |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ≤
      InnerProductGeometry.angle x y := by
  have hxI := psi_mem_Iθ x
  have hyI := psi_mem_Iθ y
  have habs : |psi x - psi y| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith [hxI.1, hxI.2, hyI.1, hyI.2, Real.pi_pos]
  have e1 : Real.arccos (Real.cos (psi x - psi y)) = |psi x - psi y| := by
    rw [← Real.cos_abs]
    exact Real.arccos_cos (abs_nonneg _) habs
  have e2 : Real.arccos (inner ℝ x y / (rho x * rho y)) = InnerProductGeometry.angle x y := by
    rw [InnerProductGeometry.angle, rho_eq_norm x, rho_eq_norm y]
  have hmain := Real.arccos_le_arccos (inner_div_le_cos_psi_sub x y hx hy)
  rw [e1, e2] at hmain
  exact hmain

end Work.ConstructionInstance
