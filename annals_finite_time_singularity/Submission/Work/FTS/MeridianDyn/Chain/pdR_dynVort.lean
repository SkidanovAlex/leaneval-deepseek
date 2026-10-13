import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst
import Submission.Work.CoreResiduals.pdR_ssVort_lam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Chain

theorem pdR_dynVort {p : ℝ} {a b σ : ℝ → ℝ} {F : Work.FTS.MeridianDyn.Fam} {r z t : ℝ}
    (hr : 0 < r) (hb : b t ≠ 0)
    (hF : Work.Cyl.DiffAt2 (fun Z Θ => F Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdR (fun r' z' => Work.FTS.MeridianDyn.dynVort p a b σ F r' z' t) r z
      = a t * (Work.Cyl.pdR (fun Z Θ => F Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (p * (Work.Cyl.rhoP r z ^ p / b t) * (r / Work.Cyl.rhoP r z ^ 2))
          - Work.Cyl.pdZ (fun Z Θ => F Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (z / Work.Cyl.rhoP r z ^ 2)) := by
  -- `∂_r ρ = r/ρ`.
  have hρ : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z) (r / Work.Cyl.rhoP r z) r := by
    have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
      have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
        simpa using (hasDerivAt_pow 2 r)
      simpa using h.const_add (z ^ 2)
    have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
    have h := hsq.sqrt hne
    have hfun : (fun r' : ℝ => Work.Cyl.rhoP r' z) = fun r' => Real.sqrt (r' ^ 2 + z ^ 2) := by
      funext r'; rw [Work.Cyl.rhoP]
    rw [hfun]
    convert h using 1
    rw [Work.Cyl.rhoP]
    field_simp
  -- `∂_r Θ = -z/ρ²`.
  have hθ : HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z)
      (-z / Work.Cyl.rhoP r z ^ 2) r := by
    have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
      have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
      have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
        funext x; simp [Pi.div_apply]
      rw [hfun] at h
      convert h using 1
      simp
    have h := hdiv.arctan
    have hfun : (fun r' : ℝ => Work.Cyl.thetaP r' z) = fun r' => Real.arctan (z / r') := by
      funext r'; rw [Work.Cyl.thetaP]
    rw [hfun]
    convert h using 1
    rw [Work.Cyl.rhoP]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  -- `∂_r (ρ^p) = p·ρ^p·(r/ρ²)`.
  have hρp : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p)
      (p * Work.Cyl.rhoP r z ^ p * (r / Work.Cyl.rhoP r z ^ 2)) r := by
    have hne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
    have h := (Real.hasDerivAt_rpow_const (x := Work.Cyl.rhoP r z) (p := p) (Or.inl hne)).comp
      r hρ
    have hfun : ((fun x : ℝ => x ^ p) ∘ fun r' => Work.Cyl.rhoP r' z)
        = fun r' => Work.Cyl.rhoP r' z ^ p := by
      funext x; rfl
    rw [hfun] at h
    convert h using 1
    rw [Real.rpow_sub_one hne]
    field_simp
  -- `∂_r (ρ^p/b t) = p·(ρ^p/b t)·(r/ρ²)`.
  have hR : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / b t)
      (p * (Work.Cyl.rhoP r z ^ p / b t) * (r / Work.Cyl.rhoP r z ^ 2)) r := by
    have h := hρp.div_const (b t)
    convert h using 1
    ring
  -- The two-variable chain rule along the radial slice.
  have hcomp := Work.Cyl.hasDerivAt_comp_two (fun Z Θ => F Z Θ (σ t))
      (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / b t) (fun r' : ℝ => Work.Cyl.thetaP r' z)
      (p * (Work.Cyl.rhoP r z ^ p / b t) * (r / Work.Cyl.rhoP r z ^ 2))
      (-z / Work.Cyl.rhoP r z ^ 2) r hF hR hθ
  have hcm := hcomp.const_mul (a t)
  rw [Work.Cyl.pdR]
  change deriv (fun r' : ℝ =>
      a t * F (Work.Cyl.rhoP r' z ^ p / b t) (Work.Cyl.thetaP r' z) (σ t)) r = _
  rw [hcm.deriv]
  ring

end Work.FTS.MeridianDyn.Chain
