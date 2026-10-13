import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
# The axial chain rule for the polar change of variables `(r,z) ↦ (ρ,θ)`

If `G` is differentiable at `(ρ(r,z), θ(r,z))`, then the axial partial derivative of
`(r,z) ↦ G(ρ(r,z), θ(r,z))` is

`∂_z (G ∘ (ρ,θ)) = sin θ · ∂_ρ G + (cos θ / ρ) · ∂_θ G`.

Indeed `∂_z ρ = z/ρ = sin θ` and `∂_z θ = r/ρ² = cos θ / ρ`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-- `z ↦ ρ(r,z) = √(r²+z²)` has derivative `z/ρ = sin θ` in the axial variable. -/
lemma hasDerivAt_rhoP_snd (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => rhoP r z') (z / rhoP r z) z := by
  have hsq : HasDerivAt (fun z' : ℝ => r ^ 2 + z' ^ 2) (2 * z) z := by
    have h : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z)
    simpa using h.const_add (r ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hfun : (fun z' : ℝ => rhoP r z') = fun z' => Real.sqrt (r ^ 2 + z' ^ 2) := by
    funext z'; rw [rhoP]
  rw [hfun]
  convert h using 1
  rw [rhoP]
  field_simp

/-- `z ↦ θ(r,z) = arctan(z/r)` has derivative `r/ρ² = cos θ / ρ` in the axial variable. -/
lemma hasDerivAt_thetaP_snd (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => thetaP r z') (r / rhoP r z ^ 2) z := by
  have hdiv : HasDerivAt (fun z' : ℝ => z' / r) (1 / r) z := by
    have h : HasDerivAt (fun z' : ℝ => z') 1 z := hasDerivAt_id z
    simpa using h.div_const r
  have h := hdiv.arctan
  have hfun : (fun z' : ℝ => thetaP r z') = fun z' => Real.arctan (z' / r) := by
    funext z'; rw [thetaP]
  rw [hfun]
  convert h using 1
  rw [rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

theorem pdZ_comp_polar_rho (G : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdZ (fun r' z' => G (Work.Cyl.rhoP r' z') (Work.Cyl.thetaP r' z')) r z =
      Real.sin (Work.Cyl.thetaP r z) * Work.Cyl.pdR G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
        + Real.cos (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z *
          Work.Cyl.pdZ G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) := by
  have hρ : rhoP r z ≠ 0 := rhoP_ne_zero hr z
  have h := hasDerivAt_comp_two G (fun z' => rhoP r z') (fun z' => thetaP r z')
      (z / rhoP r z) (r / rhoP r z ^ 2) z hG
      (hasDerivAt_rhoP_snd r z hr) (hasDerivAt_thetaP_snd r z hr)
  rw [pdZ, h.deriv, sin_thetaP hr z, cos_thetaP hr z]
  field_simp

end Work.Cyl
