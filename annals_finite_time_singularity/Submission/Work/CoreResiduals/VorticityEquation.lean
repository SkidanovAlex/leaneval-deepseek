/-
# `Work.CoreResiduals.VorticityEquation` — the spatial half of R1's dictionary

Residual **R1** is the `ℝ³` vorticity equation `∂ₜω + (u·∇)ω = (ω·∇)u` for `u = BS ω` with
`ω = solVort P`.  Its dictionary has three parts:

1. the **scalar (meridian) reduction** — for a no-swirl axisymmetric velocity
   `u = ur e_r + uz e_z` and a swirl vorticity `ω = W(r,z,t)·e_θ`, the `ℝ³` equation is equivalent to
   the scalar transport equation `∂ₜW + ur ∂_rW + uz ∂_zW = (ur/r)W` off the axis.  **This module**:
   `vorticityEquation_cylField_iff_scalar` (general profiles) and
   `vorticityEquation_psiField_iff_scalar` (stream-function form, i.e. `u = psiField ψ`);
2. the **change of variables** `(ρ,θ) → (R = ρ^α, θ) → (z = R/μ̄, θ)`, which turns the scalar
   equation into `Work.Stability.SelfSimEulerS`/`DynEq` (the profile equation of the
   construction);
3. the **elliptic identification** of `ψ` with the inverse of `ω` (`Work.Elliptic.bslOp`,
   `Work.Construction.StatEqPhi`); the existence half is the delivered
   `Work.ConstructionInstance.exists_psiField_eq_biotSavart`, and what is missing is the
   *identification* with the self-similar elliptic problem.

The `⇐` direction of (1) also covers the axis: there `eTheta` vanishes, so all the terms of the
vector equation vanish.  The equivalence needs the `DiffAt2` hypotheses on the profiles (without
them Lean's junk-valued `fderiv` makes the `⇐` direction false).
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.VorticityEquation.vorticityEquation_cylField_iff_scalar
import Submission.Work.Cyl.vorticity_psiField

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals.VorticityEquation

/-- **The scalar reduction in stream-function form**: for `u = psiField ψ` (a no-swirl axisymmetric
velocity with radial component `pdZ ψ` and axial component `-(ψ/r) - pdR ψ`) and the swirl vorticity
`ω = W(radial ·, axial ·, ·)·eTheta`, the `ℝ³` vorticity equation is equivalent to the meridian
scalar equation, provided `ψ` is `C²` and `W(·,·,t)` is differentiable in `(r,z)` off the axis. -/
theorem vorticityEquation_psiField_iff_scalar {ψ : ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ → ℝ}
    (hψ : ∀ r z : ℝ, 0 < r →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z))
    (hW : ∀ t r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => W r z t) r z) :
    Work.LWP.VorticityEquation (fun x _ => Work.Cyl.psiField ψ x)
        (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
      ↔ (∀ r z t : ℝ, 0 < r →
            deriv (fun s : ℝ => W r z s) t
              + Work.Cyl.pdZ ψ r z * Work.Cyl.pdR (fun r' z' => W r' z' t) r z
              + (-(ψ r z / r) - Work.Cyl.pdR ψ r z)
                  * Work.Cyl.pdZ (fun r' z' => W r' z' t) r z
              = (Work.Cyl.pdZ ψ r z / r) * W r z t) := by
  have h1 : ∀ t r z : ℝ, 0 < r →
      Work.Cyl.DiffAt2 (fun r z => Work.Cyl.pdZ ψ r z) r z := fun t r z hr =>
    Work.Cyl.differentiableAt_pdZ ψ r z (hψ r z hr)
  have h2 : ∀ t r z : ℝ, 0 < r →
      Work.Cyl.DiffAt2 (fun r z => -(ψ r z / r) - Work.Cyl.pdR ψ r z) r z := by
    intro t r z hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z) :=
      (hψ r z hr).differentiableAt (by norm_num)
    have hpdR : DifferentiableAt ℝ (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2) (r, z) :=
      Work.Cyl.differentiableAt_pdR ψ r z (hψ r z hr)
    show DifferentiableAt ℝ
      (fun p : ℝ × ℝ => -(ψ p.1 p.2 / p.1) - Work.Cyl.pdR ψ p.1 p.2) (r, z)
    fun_prop

  have h := vorticityEquation_cylField_iff_scalar
    (ur := fun r z _ => Work.Cyl.pdZ ψ r z)
    (uz := fun r z _ => -(ψ r z / r) - Work.Cyl.pdR ψ r z) (W := W)
    (fun t r z hr => hW t r z hr)
    (fun t r z hr => ⟨by simpa using h1 t r z hr, by simpa using h2 t r z hr⟩)
  simpa [Work.Cyl.psiField] using h

/-- **R1 from the `(ψ, W)`-decomposition: the exact remaining residual of R1.**

If the ansatz velocity is the stream-function field `psiField ψ` and the constructed vorticity is
`W(radial ·, axial ·, ·)·eTheta` — this is the *elliptic identification* of `ψ` with the inverse of
`ω`, the third part of R1's dictionary, whose existence half is the delivered
`Work.ConstructionInstance.exists_psiField_eq_biotSavart` — then residual R1 is *equivalent* to the
meridian scalar equation for `(ψ, W)`.  The scalar equation in turn is the profile equation
`Work.Stability.SelfSimEulerS`/`DynEq` read through the change of variables
`(ρ,θ) → (R = ρ^α, θ) → (z = R/μ̄, θ)`.

So R1 is precisely: **the elliptic identification** + **the profile equation**, nothing else. -/
theorem vortEq_iff_scalar_of_decomposition {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) {ψ : ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ → ℝ}
    (hv : ∀ x t, Work.ConstructionInstance.ansatzV P x t = Work.Cyl.psiField ψ x)
    (hω : ∀ x t, Work.ConstructionInstance.solVort P x t
      = W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
    (hψ : ∀ r z : ℝ, 0 < r → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z))
    (hW : ∀ t r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => W r z t) r z) :
    VortEq α P
      ↔ (∀ r z t : ℝ, 0 < r →
            deriv (fun s : ℝ => W r z s) t
              + Work.Cyl.pdZ ψ r z * Work.Cyl.pdR (fun r' z' => W r' z' t) r z
              + (-(ψ r z / r) - Work.Cyl.pdR ψ r z)
                  * Work.Cyl.pdZ (fun r' z' => W r' z' t) r z
              = (Work.Cyl.pdZ ψ r z / r) * W r z t) := by
  rw [VortEq, Work.ConstructionInstance.SelfSimVorticityEquation]
  rw [show (fun x t => Work.LWP.biotSavart (fun y => Work.ConstructionInstance.solVort P y t) x)
        = fun x _ => Work.Cyl.psiField ψ x from funext fun x => funext fun t => hv x t]
  rw [funext fun x => funext fun t => hω x t]
  exact vorticityEquation_psiField_iff_scalar hψ hW

end Work.CoreResiduals.VorticityEquation
