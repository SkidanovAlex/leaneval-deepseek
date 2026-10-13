import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Chain

theorem timeDeriv_dynVort {p : ℝ} {a b σ : ℝ → ℝ} {F : Work.FTS.MeridianDyn.Fam}
    {r z t A' B' sp fτ : ℝ}
    (ha : HasDerivAt a A' t) (hb : HasDerivAt b B' t) (hσ : HasDerivAt σ sp t)
    (hbne : b t ≠ 0)
    (hG : Work.Cyl.DiffAt2 (fun Z s => F Z (Work.Cyl.thetaP r z) s)
      (Work.Cyl.rhoP r z ^ p / b t) (σ t))
    (hfτ : HasDerivAt (fun s => F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) s)
      fτ (σ t)) :
    deriv (fun s => Work.FTS.MeridianDyn.dynVort p a b σ F r z s) t
      = A' * F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)
        + a t * (sp * fτ - (B' / b t) * (Work.Cyl.rhoP r z ^ p / b t)
            * Work.Cyl.pdR (fun Z Θ => F Z Θ (σ t))
                (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)) := by
  -- the derivative of the rescaled radial variable `s ↦ ρ^p / b s`
  have hZ : HasDerivAt (fun s : ℝ => Work.Cyl.rhoP r z ^ p / b s)
      (-(B' / b t) * (Work.Cyl.rhoP r z ^ p / b t)) t := by
    have h0 : HasDerivAt (fun s : ℝ => Work.Cyl.rhoP r z ^ p * (b s)⁻¹)
        (Work.Cyl.rhoP r z ^ p * (-B' / (b t) ^ 2)) t :=
      (hb.inv hbne).const_mul (Work.Cyl.rhoP r z ^ p)
    have hfun : (fun s : ℝ => Work.Cyl.rhoP r z ^ p * (b s)⁻¹)
        = fun s : ℝ => Work.Cyl.rhoP r z ^ p / b s := by
      funext s; rw [div_eq_mul_inv]
    have hval : Work.Cyl.rhoP r z ^ p * (-B' / (b t) ^ 2)
        = -(B' / b t) * (Work.Cyl.rhoP r z ^ p / b t) := by
      field_simp
    rw [hfun, hval] at h0
    exact h0
  -- the chain rule in the two fake-time variables `(Z, S) = (ρ^p/b, σ)`
  have hcomp : HasDerivAt
      (fun s : ℝ => F (Work.Cyl.rhoP r z ^ p / b s) (Work.Cyl.thetaP r z) (σ s))
      (Work.Cyl.pdR (fun Z S => F Z (Work.Cyl.thetaP r z) S)
          (Work.Cyl.rhoP r z ^ p / b t) (σ t)
          * (-(B' / b t) * (Work.Cyl.rhoP r z ^ p / b t))
        + Work.Cyl.pdZ (fun Z S => F Z (Work.Cyl.thetaP r z) S)
            (Work.Cyl.rhoP r z ^ p / b t) (σ t) * sp) t :=
    Work.Cyl.hasDerivAt_comp_two (fun Z S => F Z (Work.Cyl.thetaP r z) S)
      (fun s : ℝ => Work.Cyl.rhoP r z ^ p / b s) σ
      (-(B' / b t) * (Work.Cyl.rhoP r z ^ p / b t)) sp t hG hZ hσ
  have hprod : HasDerivAt
      (fun s : ℝ => a s * F (Work.Cyl.rhoP r z ^ p / b s) (Work.Cyl.thetaP r z) (σ s))
      (A' * F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)
        + a t * (Work.Cyl.pdR (fun Z S => F Z (Work.Cyl.thetaP r z) S)
            (Work.Cyl.rhoP r z ^ p / b t) (σ t)
            * (-(B' / b t) * (Work.Cyl.rhoP r z ^ p / b t))
          + Work.Cyl.pdZ (fun Z S => F Z (Work.Cyl.thetaP r z) S)
              (Work.Cyl.rhoP r z ^ p / b t) (σ t) * sp)) t := ha.mul hcomp
  -- the fake-time derivative of the slice is `fτ` (the `S`-partial), and the `Z`-partial is the
  -- partial of the frozen slice at `σ t` (definitionally)
  have hpdZ : Work.Cyl.pdZ (fun Z S => F Z (Work.Cyl.thetaP r z) S)
      (Work.Cyl.rhoP r z ^ p / b t) (σ t) = fτ := by
    simp only [Work.Cyl.pdZ, hfτ.deriv]
  have hpdR : Work.Cyl.pdR (fun Z S => F Z (Work.Cyl.thetaP r z) S)
      (Work.Cyl.rhoP r z ^ p / b t) (σ t)
      = Work.Cyl.pdR (fun Z Θ' => F Z Θ' (σ t)) (Work.Cyl.rhoP r z ^ p / b t)
          (Work.Cyl.thetaP r z) := by
    simp only [Work.Cyl.pdR]
  rw [show (fun s : ℝ => Work.FTS.MeridianDyn.dynVort p a b σ F r z s)
      = (fun s : ℝ => a s * F (Work.Cyl.rhoP r z ^ p / b s) (Work.Cyl.thetaP r z) (σ s))
      from rfl]
  rw [hprod.deriv, hpdZ, hpdR]
  ring

end Work.FTS.MeridianDyn.Chain
