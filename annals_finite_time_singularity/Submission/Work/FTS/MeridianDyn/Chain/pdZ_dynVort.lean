import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.CoreResiduals.pdZ_ssVort_lam
import Submission.Work.Cyl.hasDerivAt_rhoP_rpow_div_snd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Chain

theorem pdZ_dynVort {p : ℝ} {a b σ : ℝ → ℝ} {F : Work.FTS.MeridianDyn.Fam} {r z t : ℝ}
    (hr : 0 < r) (hb : b t ≠ 0)
    (hF : Work.Cyl.DiffAt2 (fun Z Θ => F Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdZ (fun r' z' => Work.FTS.MeridianDyn.dynVort p a b σ F r' z' t) r z
      = a t * (Work.Cyl.pdR (fun Z Θ => F Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
          + Work.Cyl.pdZ (fun Z Θ => F Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (r / Work.Cyl.rhoP r z ^ 2)) := by
  -- The two-variable chain rule for `z' ↦ F (ρ(r,z')^p/b t) (Θ(r,z')) (σ t)` at `(ρ^p/b t, Θ)`.
  have hchain := Work.Cyl.hasDerivAt_comp_two (fun Z Θ => F Z Θ (σ t))
    (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / b t) (fun z' : ℝ => Work.Cyl.thetaP r z')
    (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
    (r / Work.Cyl.rhoP r z ^ 2) z hF
    (Work.Cyl.hasDerivAt_rhoP_rpow_div_snd r p z (b t) hr)
    (Work.Cyl.hasDerivAt_thetaP_snd r z hr)
  -- Pull the amplitude prefactor `a t` out of the derivative and unfold `dynVort` and `pdZ`.
  have hmain := hchain.const_mul (a t)
  rw [Work.Cyl.pdZ]
  show deriv (fun z' : ℝ =>
      a t * F (Work.Cyl.rhoP r z' ^ p / b t) (Work.Cyl.thetaP r z') (σ t)) z = _
  rw [hmain.deriv]

end Work.FTS.MeridianDyn.Chain
