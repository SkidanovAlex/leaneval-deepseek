/-
# `Work.R1G.vortEqWithDeficit_iff_meridian` — the meridian dictionary for the *deficit* form of R1

Residual **R1** in its honest (deficit-carrying) form is

  `∂ₜω + (u·∇)ω = (ω·∇)u + Def`,    `u = BS ω = psiField ψ`,  `ω = W(radial ·, axial ·, t)·e_θ`,

`Work.CoreResiduals.VortEqWithDeficit P Def`.  The *spatial* half of the dictionary
(`Work.CoreResiduals.VorticityEquation.vortEq_iff_scalar_of_decomposition`) identifies the
zero-deficit case with the meridian scalar equation for `(ψ, W)`; this file extends that dictionary
to an arbitrary deficit of swirl type, `Def = WD(radial ·, axial ·, t)·e_θ`:

  `VortEqWithDeficit P (WD·e_θ)  ⟺  meridianResid W ψ = WD`   (on `r > 0`).

The point is that for a swirl vorticity the *whole* `ℝ³` residual is `scalar·e_θ`, so any deficit
of the ansatz's own shape is carried by the meridian residual with no loss: the deficit is an
honest `(r,z,t)`-function, exactly as the G-route's `Work.R1G.HonestR1` / `DeficitIsGResidual`
identification needs.

## How it is proved

* `Work.R1G.vecResid_eq_scalar_smul` (delegated) is the pointwise identity

  `∂ₜω + (u·∇)ω - (ω·∇)u = (∂ₜW + u_r ∂_rW + u_z ∂_zW - (u_r/r)W) • e_θ`

  for an arbitrary no-swirl velocity `u = cylField ur uz`; it is the deficit refinement of
  `vorticityEquation_cylField_iff_scalar`, valid also on the axis (where `e_θ = 0` and both sides
  vanish).
* Instantiating it at `u_r = ∂_zψ`, `u_z = -(ψ/r) - ∂_rψ` (i.e. `u = psiField ψ`) turns the
  bracket into `Work.CoreResiduals.meridianResid W (fun r z _ => ψ r z)`, giving the pointwise
  identity `hident` below.
* `VortEqWithDeficit` is then unfolded and rewritten along `hv` (the Biot–Savart velocity is
  `psiField ψ`) and `hω` (`solVort P` is `W·e_θ`), reducing the vector statement to
  `∀ x t, hident x t` with the deficit `WD·e_θ`.
* The two directions are then: evaluate at the meridian point `(r, 0, z)` (`work.R1G.mkPt`) and
  read off the `e_1`-component for `⟹` (the common `directionalDeriv` term cancels by
  `add_left_cancel`), and use the scalar equation at `(radial x, axial x)` for `⟸` (the axis case
  being automatic since `e_θ x = 0`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.R1G.Defs
import Submission.Work.R1G.vecResid_eq_scalar_smul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

theorem vortEqWithDeficit_iff_meridian {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {ψ : ℝ → ℝ → ℝ} {W WD : ℝ → ℝ → ℝ → ℝ}
    (hv : ∀ x t, Work.ConstructionInstance.ansatzV P x t = Work.Cyl.psiField ψ x)
    (hω : ∀ x t, Work.ConstructionInstance.solVort P x t
      = W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
    (hψ : ∀ r z : ℝ, 0 < r → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z))
    (hW : ∀ t r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => W r z t) r z) :
    Work.CoreResiduals.VortEqWithDeficit P
        (fun x t => WD (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
      ↔ ∀ r z t : ℝ, 0 < r →
          Work.CoreResiduals.meridianResid W (fun r z _ => ψ r z) r z t = WD r z t := by
  -- `ψ`'s reduced profiles are `DiffAt2` off the axis, so `psiField ψ` is a legitimate
  -- `cylField` for the pointwise identity.
  have h1 : ∀ r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => Work.Cyl.pdZ ψ r z) r z :=
    fun r z hr => Work.Cyl.differentiableAt_pdZ ψ r z (hψ r z hr)
  have h2 : ∀ r z : ℝ, 0 < r →
      Work.Cyl.DiffAt2 (fun r z => -(ψ r z / r) - Work.Cyl.pdR ψ r z) r z := by
    intro r z hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z) :=
      (hψ r z hr).differentiableAt (by norm_num)
    have hpdR : DifferentiableAt ℝ (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2) (r, z) :=
      Work.Cyl.differentiableAt_pdR ψ r z (hψ r z hr)
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => -(ψ p.1 p.2 / p.1) - Work.Cyl.pdR ψ p.1 p.2) (r, z)
    fun_prop
  -- The pointwise meridian identity: the residual of the swirl field is `meridianResid • e_θ`.
  have hident : ∀ x : Work.Cyl.R3, ∀ t : ℝ,
      (FiniteTimeSingularity.timeDeriv
          (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
        + FiniteTimeSingularity.directionalDeriv
            (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
            (fun x _ => Work.Cyl.psiField ψ x) x t)
      = (FiniteTimeSingularity.directionalDeriv (fun x _ => Work.Cyl.psiField ψ x)
            (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
          + (Work.CoreResiduals.meridianResid W (fun r z _ => ψ r z)
              (Work.Cyl.radial x) (Work.Cyl.axial x) t) • Work.Cyl.eTheta x) := by
    intro x t
    have hb := vecResid_eq_scalar_smul (ur := fun r z _ => Work.Cyl.pdZ ψ r z)
        (uz := fun r z _ => -(ψ r z / r) - Work.Cyl.pdR ψ r z) (W := W) hW
        (fun t r z hr => ⟨h1 r z hr, h2 r z hr⟩) x t
    simpa only [Work.Cyl.psiField, Work.CoreResiduals.meridianResid] using hb
  -- Unfold `VortEqWithDeficit` and substitute the hypotheses `hv`, `hω`.
  have key : Work.CoreResiduals.VortEqWithDeficit P
        (fun x t => WD (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
      ↔ ∀ x : Work.Cyl.R3, ∀ t : ℝ,
          (FiniteTimeSingularity.timeDeriv
              (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
            + FiniteTimeSingularity.directionalDeriv
                (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
                (fun x _ => Work.Cyl.psiField ψ x) x t)
          = (FiniteTimeSingularity.directionalDeriv (fun x _ => Work.Cyl.psiField ψ x)
                (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
              + WD (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) := by
    have hbv : (fun x t => Work.LWP.biotSavart
          (fun y => Work.ConstructionInstance.solVort P y t) x)
        = (fun x _ => Work.Cyl.psiField ψ x) := funext fun x => funext fun t => hv x t
    have hsω : Work.ConstructionInstance.solVort P
        = (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) :=
      funext fun x => funext fun t => hω x t
    simp only [Work.CoreResiduals.VortEqWithDeficit]
    rw [hbv, hsω]
  rw [key]
  constructor
  · -- `⟹`: evaluate at the meridian point and read the `e_1`-component.
    intro h r z t hr
    have hx := h (mkPt r z) t
    rw [hident (mkPt r z) t] at hx
    rw [radial_mkPt, abs_of_pos hr, axial_mkPt] at hx
    have he : (FiniteTimeSingularity.e 1 : Work.Cyl.R3) = Work.Cyl.e1 := rfl
    rw [eTheta_mkPt hr, he] at hx
    have hx' := add_left_cancel hx
    have hx1 := congrArg (fun v : Work.Cyl.R3 => v 1) hx'
    simpa only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Work.Cyl.e1_apply_one, mul_one]
      using hx1
  · -- `⟸`: use the scalar equation at `(radial x, axial x)`; on the axis both sides vanish.
    intro h x t
    rw [hident x t]
    by_cases hr : 0 < Work.Cyl.radial x
    · rw [h (Work.Cyl.radial x) (Work.Cyl.axial x) t hr]
    · have hr0 : Work.Cyl.radial x = 0 :=
        le_antisymm (not_lt.mp hr) (Work.Cyl.radial_nonneg x)
      rw [show Work.Cyl.eTheta x = 0 from by simp [Work.Cyl.eTheta, hr0], smul_zero, smul_zero]

end Work.R1G
