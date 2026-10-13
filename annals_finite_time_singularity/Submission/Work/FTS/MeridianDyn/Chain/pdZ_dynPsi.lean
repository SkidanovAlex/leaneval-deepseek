import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.CoreResiduals.pdR_ssPsi_lam
import Submission.Work.Cyl.pdZ_comp_polar
import Submission.Work.Cyl.pdZ_comp_polar_rho
import Submission.Work.Cyl.hasDerivAt_rhoP_rpow_div_snd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The axial chain rule for the dynamic stream-function ansatz `dynPsi`

`Work.FTS.MeridianDyn.dynPsi p a b σ Φ r z t = ρ(r,z)² · a(t) · Φ (ρ(r,z)^p/b(t)) (θ(r,z)) (σ t)`
with `ρ = √(r²+z²)` and `θ = arctan(z/r)`.  Since

* `∂_z (ρ²) = 2·ρ·∂_zρ = 2z`,
* `∂_z (ρ^p/b) = p · (ρ^p/b) · (z/ρ²)` (`Work.Cyl.hasDerivAt_rhoP_rpow_div_snd`), and
* `∂_z θ = r/ρ²` (`Work.Cyl.hasDerivAt_thetaP_snd`),

the product rule together with the two-variable chain rule (`Work.Cyl.hasDerivAt_comp_two`) gives
the axial chain rule of the dynamic ansatz; this is the `σ`/`b`-dependent generalisation of
`Work.CoreResiduals.pdZ_ssPsi_lam` (the constant-rate case `lam = b`, `a = b⁻¹`, `σ = id`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.FTS.MeridianDyn.Chain

theorem pdZ_dynPsi {p : ℝ} {a b σ : ℝ → ℝ} {Φ : Work.FTS.MeridianDyn.Fam} {r z t : ℝ}
    (hr : 0 < r) (hb : b t ≠ 0)
    (hΦ : Work.Cyl.DiffAt2 (fun Z Θ => Φ Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdZ (fun r' z' => Work.FTS.MeridianDyn.dynPsi p a b σ Φ r' z' t) r z
      = a t * (2 * z * Φ (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)
          + Work.Cyl.rhoP r z ^ 2 *
              (Work.Cyl.pdR (fun Z Θ => Φ Z Θ (σ t))
                  (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
                  * (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
                + Work.Cyl.pdZ (fun Z Θ => Φ Z Θ (σ t))
                    (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
                    * (r / Work.Cyl.rhoP r z ^ 2))) := by
  have hne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  -- the two-variable chain rule for `z' ↦ Φ (ρ(r,z')^p/b t) (θ(r,z')) (σ t)`
  have hchain : HasDerivAt
      (fun z' : ℝ => Φ (Work.Cyl.rhoP r z' ^ p / b t) (Work.Cyl.thetaP r z') (σ t))
      (Work.Cyl.pdR (fun Z Θ => Φ Z Θ (σ t))
          (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
          * (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
        + Work.Cyl.pdZ (fun Z Θ => Φ Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (r / Work.Cyl.rhoP r z ^ 2)) z :=
    Work.Cyl.hasDerivAt_comp_two (fun Z Θ => Φ Z Θ (σ t))
      (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / b t) (fun z' : ℝ => Work.Cyl.thetaP r z')
      (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
      (r / Work.Cyl.rhoP r z ^ 2) z hΦ
      (Work.Cyl.hasDerivAt_rhoP_rpow_div_snd r p z (b t) hr)
      (Work.Cyl.hasDerivAt_thetaP_snd r z hr)
  -- multiply by the outer amplitude `a t`
  have hpsi : HasDerivAt
      (fun z' : ℝ => a t * Φ (Work.Cyl.rhoP r z' ^ p / b t) (Work.Cyl.thetaP r z') (σ t))
      (a t * (Work.Cyl.pdR (fun Z Θ => Φ Z Θ (σ t))
          (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
          * (p * (Work.Cyl.rhoP r z ^ p / b t) * (z / Work.Cyl.rhoP r z ^ 2))
        + Work.Cyl.pdZ (fun Z Θ => Φ Z Θ (σ t))
            (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
            * (r / Work.Cyl.rhoP r z ^ 2))) z :=
    hchain.const_mul (a t)
  -- `∂_z (ρ²) = 2·ρ·(z/ρ) = 2z`
  have hsq : HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) (2 * z) z := by
    have h := (Work.Cyl.hasDerivAt_rhoP_snd r z hr).pow 2
    rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one] at h
    have hval : 2 * Work.Cyl.rhoP r z * (z / Work.Cyl.rhoP r z) = 2 * z := by
      field_simp
    exact h.congr_deriv hval
  -- product rule
  have hprod := hsq.mul hpsi
  rw [Work.Cyl.pdZ]
  rw [show (fun z' : ℝ => Work.FTS.MeridianDyn.dynPsi p a b σ Φ r z' t)
      = ((fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) *
          fun z' : ℝ => a t * Φ (Work.Cyl.rhoP r z' ^ p / b t)
            (Work.Cyl.thetaP r z') (σ t)) from by
        funext z'
        simp only [Work.FTS.MeridianDyn.dynPsi_apply, Pi.mul_apply]
        ring]
  rw [hprod.deriv]
  ring

end Work.FTS.MeridianDyn.Chain
