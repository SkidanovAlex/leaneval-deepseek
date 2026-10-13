import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.CoreResiduals.SelfSimReduction

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

theorem timeDeriv_ssVort_lam {p κ : ℝ} {lam : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {r z t : ℝ}
    (hlam : lam t ≠ 0) (hderiv : HasDerivAt lam (-κ) t)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) :
    deriv (fun s : ℝ => Work.CoreResiduals.ssVort p lam F r z s) t =
      κ * ((lam t) ^ 2)⁻¹ *
        (F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
          + (Work.Cyl.rhoP r z ^ p / lam t)
              * Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) := by
  have hinv : HasDerivAt (fun s : ℝ => (lam s)⁻¹) (κ * ((lam t)^2)⁻¹) t := by
    have h := hderiv.inv hlam
    convert h using 1
    ring
  have hR : HasDerivAt (fun s : ℝ => Work.Cyl.rhoP r z ^ p / lam s)
      (Work.Cyl.rhoP r z ^ p * (κ * ((lam t)^2)⁻¹)) t := by
    have h : HasDerivAt (fun s : ℝ => Work.Cyl.rhoP r z ^ p * (lam s)⁻¹)
        (Work.Cyl.rhoP r z ^ p * (κ * ((lam t)^2)⁻¹)) t := hinv.const_mul _
    simpa only [div_eq_mul_inv] using h
  have hZ : HasDerivAt (fun _ : ℝ => Work.Cyl.thetaP r z) 0 t := hasDerivAt_const t _
  have hcomp : HasDerivAt (fun s : ℝ => F (Work.Cyl.rhoP r z ^ p / lam s) (Work.Cyl.thetaP r z))
      (Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
        * (Work.Cyl.rhoP r z ^ p * (κ * ((lam t)^2)⁻¹))) t := by
    have h := Work.Cyl.hasDerivAt_comp_two F (fun s : ℝ => Work.Cyl.rhoP r z ^ p / lam s)
      (fun _ : ℝ => Work.Cyl.thetaP r z) (Work.Cyl.rhoP r z ^ p * (κ * ((lam t)^2)⁻¹)) 0 t
      hF hR hZ
    simpa using h
  have hprod : HasDerivAt
      (fun s : ℝ => (lam s)⁻¹ * F (Work.Cyl.rhoP r z ^ p / lam s) (Work.Cyl.thetaP r z))
      (κ * ((lam t)^2)⁻¹ * F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
        + (lam t)⁻¹ * (Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
            * (Work.Cyl.rhoP r z ^ p * (κ * ((lam t)^2)⁻¹)))) t := hinv.mul hcomp
  rw [show (fun s : ℝ => Work.CoreResiduals.ssVort p lam F r z s) =
      (fun s : ℝ => (lam s)⁻¹ * F (Work.Cyl.rhoP r z ^ p / lam s) (Work.Cyl.thetaP r z)) from rfl]
  rw [hprod.deriv]
  ring_nf

end Work.CoreResiduals
