import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.CoreResiduals.SelfSimReduction

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

open Work.Cyl

/-- Radial chain rule for the self-similar vorticity
`W = λ(t)⁻¹·F(ρ(r,z)^p/λ(t), Θ(r,z))`: the `∂_r` of `ssVort` is obtained from `F` at the
self-similar coordinates by the two-variable chain rule, using
`∂_r(ρ^p/λ) = p·(ρ^p/λ)·(r/ρ²)` and `∂_r Θ = -z/ρ²`. -/
theorem pdR_ssVort_lam {p : ℝ} {lam : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {r z t : ℝ}
    (hr : 0 < r) (hlam : lam t ≠ 0)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdR (fun r' z' => Work.CoreResiduals.ssVort p lam F r' z' t) r z =
      (lam t)⁻¹ *
        (Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
            * (p * (Work.Cyl.rhoP r z ^ p / lam t) * (r / Work.Cyl.rhoP r z ^ 2))
          - Work.Cyl.pdZ F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
              * (z / Work.Cyl.rhoP r z ^ 2)) := by
  -- `∂_r ρ = r/ρ`.
  have hρ : HasDerivAt (fun r' : ℝ => rhoP r' z) (r / rhoP r z) r := by
    have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
      have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
        simpa using (hasDerivAt_pow 2 r)
      simpa using h.const_add (z ^ 2)
    have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
    have h := hsq.sqrt hne
    have hfun : (fun r' : ℝ => rhoP r' z) = fun r' => Real.sqrt (r' ^ 2 + z ^ 2) := by
      funext r'; rw [rhoP]
    rw [hfun]
    convert h using 1
    rw [rhoP]
    field_simp
  -- `∂_r Θ = -z/ρ²`.
  have hθ : HasDerivAt (fun r' : ℝ => thetaP r' z) (-z / rhoP r z ^ 2) r := by
    have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
      have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
      have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
        funext x; simp [Pi.div_apply]
      rw [hfun] at h
      convert h using 1
      simp
    have h := hdiv.arctan
    have hfun : (fun r' : ℝ => thetaP r' z) = fun r' => Real.arctan (z / r') := by
      funext r'; rw [thetaP]
    rw [hfun]
    convert h using 1
    rw [rhoP]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  -- `∂_r (ρ^p) = p·ρ^p·(r/ρ²)`.
  have hρp : HasDerivAt (fun r' : ℝ => rhoP r' z ^ p)
      (p * rhoP r z ^ p * (r / rhoP r z ^ 2)) r := by
    have hne : rhoP r z ≠ 0 := rhoP_ne_zero hr z
    have h := (Real.hasDerivAt_rpow_const (x := rhoP r z) (p := p) (Or.inl hne)).comp r hρ
    have hfun : ((fun x : ℝ => x ^ p) ∘ fun r' => rhoP r' z) = fun r' => rhoP r' z ^ p := by
      funext x; rfl
    rw [hfun] at h
    convert h using 1
    rw [Real.rpow_sub_one hne]
    field_simp
  -- `∂_r (ρ^p/λ(t)) = p·(ρ^p/λ(t))·(r/ρ²)`.
  have hR : HasDerivAt (fun r' : ℝ => rhoP r' z ^ p / lam t)
      (p * (rhoP r z ^ p / lam t) * (r / rhoP r z ^ 2)) r := by
    have h := hρp.div_const (lam t)
    convert h using 1
    ring
  -- the two-variable chain rule along the radial slice.
  have hcomp := hasDerivAt_comp_two F
      (fun r' : ℝ => rhoP r' z ^ p / lam t) (fun r' : ℝ => thetaP r' z)
      (p * (rhoP r z ^ p / lam t) * (r / rhoP r z ^ 2))
      (-z / rhoP r z ^ 2) r hF hR hθ
  have hcm := hcomp.const_mul (lam t)⁻¹
  rw [pdR]
  change deriv (fun r' : ℝ => (lam t)⁻¹ * F (rhoP r' z ^ p / lam t) (thetaP r' z)) r = _
  rw [hcm.deriv]
  ring

end Work.CoreResiduals
