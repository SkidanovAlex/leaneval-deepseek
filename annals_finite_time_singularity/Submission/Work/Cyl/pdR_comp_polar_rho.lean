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

namespace Work.Cyl

theorem pdR_comp_polar_rho (G : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdR (fun r' z' => G (Work.Cyl.rhoP r' z') (Work.Cyl.thetaP r' z')) r z =
      Real.cos (Work.Cyl.thetaP r z) * Work.Cyl.pdR G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
        - Real.sin (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z *
          Work.Cyl.pdZ G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) := by
  -- The radial partial derivative of the polar pair `r' ↦ (ρ(r', z), θ(r', z))`,
  -- combined with the chain rule for a two-variable function, gives the claim.
  -- Step 1: `∂_r ρ(r', z) = r / ρ(r, z)`.
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    have h := (hasDerivAt_pow 2 r).add_const (z ^ 2)
    simpa using h
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have hR : HasDerivAt (fun r' : ℝ => rhoP r' z) (r / rhoP r z) r := by
    have h := hsq.sqrt hne
    have hval : (2 * r) / (2 * Real.sqrt (r ^ 2 + z ^ 2)) = r / rhoP r z := by
      rw [rhoP]; field_simp
    rw [hval] at h
    exact h
  -- Step 2: `∂_r θ(r', z) = -z / (r² + z²) = -sin θ / ρ`.
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have hinv : HasDerivAt (fun r' : ℝ => (r')⁻¹) (-(r ^ 2)⁻¹) r :=
      hasDerivAt_inv (ne_of_gt hr)
    have h := hinv.const_mul z
    have hval : z * (-(r ^ 2)⁻¹) = -z / r ^ 2 := by rw [div_eq_mul_inv]; ring
    rw [hval] at h
    exact h
  have hT : HasDerivAt (fun r' : ℝ => thetaP r' z) (-z / (r ^ 2 + z ^ 2)) r := by
    have h := (Real.hasDerivAt_arctan (z / r)).comp r hdiv
    have hval : 1 / (1 + (z / r) ^ 2) * (-z / r ^ 2) = -z / (r ^ 2 + z ^ 2) := by
      field_simp
    rw [hval] at h
    exact h
  -- Step 3: rewrite `-z/(r²+z²)` as `-sin θ / ρ` and `r/ρ` as `cos θ`.
  have hid : -z / (r ^ 2 + z ^ 2) = -(Real.sin (thetaP r z) / rhoP r z) := by
    rw [sin_thetaP hr z]
    have hρ : rhoP r z ≠ 0 := rhoP_ne_zero hr z
    field_simp
    rw [rhoP_sq]
  -- Step 4: chain rule along the radial slice.
  have hcomp := hasDerivAt_comp_two G (fun r' : ℝ => rhoP r' z)
    (fun r' : ℝ => thetaP r' z) (r / rhoP r z) (-z / (r ^ 2 + z ^ 2)) r hG hR hT
  rw [pdR]
  change deriv (fun t : ℝ => G (rhoP t z) (thetaP t z)) r = _
  rw [hcomp.deriv, hid, cos_thetaP hr z]
  ring

end Work.Cyl
