import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The axial chain rule for `(r,z) ↦ F(ρ(r,z)^α, θ(r,z))`

If `F` is differentiable at `(ρ(r,z)^α, θ(r,z))` and `r > 0`, then the axial partial derivative of
`(r,z) ↦ F(ρ(r,z)^α, θ(r,z))` is

`∂_z = (sin θ / ρ) · (α ρ^α ∂_ρ F) + (cos θ / ρ) · ∂_θ F`.

Indeed `∂_z (ρ^α) = α ρ^{α-1} ∂_z ρ = α ρ^{α-1} · z/ρ = (α ρ^α) · sin θ / ρ`, using
`∂_z ρ = z/ρ = sin θ`, and `∂_z θ = r/ρ² = (cos θ)/ρ`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-- `z ↦ ρ(r,z) = √(r²+z²)` has derivative `z/ρ = sin θ` in the axial variable. -/
lemma hasDerivAt_rhoP_polar (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => rhoP r z') (z / rhoP r z) z := by
  have hsq : HasDerivAt (fun z' : ℝ => r ^ 2 + z' ^ 2) (2 * z) z := by
    have h : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z)
    simpa using h.const_add (r ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hval : (2 * z) / (2 * Real.sqrt (r ^ 2 + z ^ 2)) = z / rhoP r z := by
    have hs : Real.sqrt (r ^ 2 + z ^ 2) ≠ 0 := by positivity
    rw [rhoP]; field_simp
  rw [hval] at h
  exact h

/-- `z ↦ θ(r,z) = arctan(z/r)` has derivative `r/ρ² = cos θ / ρ` in the axial variable. -/
lemma hasDerivAt_thetaP_polar (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => thetaP r z') (r / (r ^ 2 + z ^ 2)) z := by
  have hlin : HasDerivAt (fun z' : ℝ => z' / r) (1 / r) z := by
    simpa using (hasDerivAt_id z).div_const r
  have h := (Real.hasDerivAt_arctan (z / r)).comp z hlin
  have hval : 1 / (1 + (z / r) ^ 2) * (1 / r) = r / (r ^ 2 + z ^ 2) := by
    field_simp
  rw [hval] at h
  exact h

/-- `z ↦ ρ(r,z)^α` has derivative `α ρ^{α-1} · z/ρ`. -/
lemma hasDerivAt_rhoP_rpow_polar (r α z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => rhoP r z' ^ α) (α * rhoP r z ^ (α - 1) * (z / rhoP r z)) z := by
  have hbase := hasDerivAt_rhoP_polar r z hr
  have h := hbase.rpow_const (p := α) (Or.inl (ne_of_gt (rhoP_pos hr z)))
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

theorem pdZ_comp_polar (F : ℝ → ℝ → ℝ) (α r z : ℝ) (hr : 0 < r)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdZ (fun r' z' => F (Work.Cyl.rhoP r' z' ^ α) (Work.Cyl.thetaP r' z')) r z =
      Real.sin (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z *
          (α * Work.Cyl.rhoP r z ^ α * Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z))
        + Real.cos (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z *
          Work.Cyl.pdZ F (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
  have hR := hasDerivAt_rhoP_rpow_polar r α z hr
  have hZ := hasDerivAt_thetaP_polar r z hr
  have h := hasDerivAt_comp_two F (fun t : ℝ => rhoP r t ^ α) (fun t : ℝ => thetaP r t)
      (α * rhoP r z ^ (α - 1) * (z / rhoP r z)) (r / (r ^ 2 + z ^ 2)) z hF hR hZ
  have hpd : pdZ (fun r' z' => F (rhoP r' z' ^ α) (thetaP r' z')) r z =
      deriv (fun t : ℝ => F (rhoP r t ^ α) (thetaP r t)) z := rfl
  rw [hpd, h.deriv]
  rw [sin_thetaP hr z, cos_thetaP hr z]
  have hpow : rhoP r z ^ α = rhoP r z ^ (α - 1) * rhoP r z := by
    conv_lhs => rw [show α = (α - 1) + 1 by ring]
    rw [Real.rpow_add (rhoP_pos hr z), Real.rpow_one]
  rw [hpow, ← rhoP_sq r z]
  field_simp

end Work.Cyl
