/-
# `Work.R1G.vortEqWithDeficit_iff_meridian_field` — the meridian dictionary for the *deficit*
form of R1, with a time-dependent stream function

Residual **R1** in its honest (deficit-carrying) form is

  `∂ₜω + (u·∇)ω = (ω·∇)u + Def`,   `u = BS ω`,  `ω = W(radial ·, axial ·, t)·e_θ`,

i.e. `Work.CoreResiduals.VortEqWithDeficit P Def`.  When the Biot–Savart velocity of the ansatz is
the stream-function field of a (possibly `t`-dependent) stream function `Ψ`,

  `ansatzV P x t = psiField (Ψ · · t) x`
    `= cylField (∂_zΨ(·,·,t)) (-(Ψ(·,·,t)/r) - ∂_rΨ(·,·,t)) x`,

the *whole* `ℝ³` residual is `scalar·e_θ` where the scalar is exactly the meridian residual
`Work.CoreResiduals.meridianResid W Ψ`.  Hence an arbitrary swirl-type deficit
`Def = WD(radial ·, axial ·, t)·e_θ` is carried, with no loss, by the meridian residual:

  `VortEqWithDeficit P (WD·e_θ)  ⟺  meridianResid W Ψ = WD`  on `r > 0`.

## How it is proved

* `Work.R1G.vecResid_eq_scalar_smul` (proved in this directory) is the pointwise identity

  `∂ₜω + (u·∇)ω - (ω·∇)u = (∂ₜW + u_r ∂_rW + u_z ∂_zW - (u_r/r)W) • e_θ`

  for an arbitrary no-swirl velocity `u = cylField ur uz`, valid also on the axis (where `e_θ = 0`
  and both sides vanish).
* Instantiating it at `u_r = ∂_zΨ(·,·,t)`, `u_z = -(Ψ/r) - ∂_rΨ(·,·,t)` turns the bracket into
  `meridianResid W Ψ`, giving the pointwise identity `hident` below.
* `VortEqWithDeficit` is then unfolded and rewritten along `hv` (the Biot–Savart velocity, which is
  `ansatzV P` definitionally, is the `cylField` of the reduced profiles) and `hω`
  (`solVort P = W·e_θ`), reducing the vector statement to `∀ x t, hident x t` with deficit `WD·e_θ`.
* The two directions are then: evaluate at the meridian point `(r,0,z)` (`Work.R1G.mkPt`) and read
  off the `e_1`-component for `⟹` (the common `directionalDeriv` term cancels by `add_left_cancel`),
  and use the scalar equation at `(radial x, axial x)` for `⟸` (the axis case being automatic since
  `e_θ x = 0`).
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

theorem vortEqWithDeficit_iff_meridian_field {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {Ψ : ℝ → ℝ → ℝ → ℝ} {W WD : ℝ → ℝ → ℝ → ℝ}
    (hv : ∀ x t, Work.ConstructionInstance.ansatzV P x t = Work.Cyl.cylField
        (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
        (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x)
    (hω : ∀ x t, Work.ConstructionInstance.solVort P x t
      = W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
    (hΨ : ∀ t r z : ℝ, 0 < r →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2 t) (r, z))
    (hW : ∀ t r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => W r z t) r z) :
    Work.CoreResiduals.VortEqWithDeficit P
        (fun x t => WD (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
      ↔ ∀ r z t : ℝ, 0 < r →
          Work.CoreResiduals.meridianResid W Ψ r z t = WD r z t := by
  -- The reduced profiles `∂_zΨ(·,·,t)` and `-(Ψ/r) - ∂_rΨ(·,·,t)` are `DiffAt2` off the axis.
  have h1 : ∀ t r z : ℝ, 0 < r →
      Work.Cyl.DiffAt2 (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z) r z :=
    fun t r z hr => Work.Cyl.differentiableAt_pdZ (fun r z => Ψ r z t) r z (hΨ t r z hr)
  have h2 : ∀ t r z : ℝ, 0 < r →
      Work.Cyl.DiffAt2
        (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) r z := by
    intro t r z hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => Ψ p.1 p.2 t) (r, z) :=
      (hΨ t r z hr).differentiableAt (by norm_num)
    have hpdR : DifferentiableAt ℝ
        (fun p : ℝ × ℝ => Work.Cyl.pdR (fun r z => Ψ r z t) p.1 p.2) (r, z) :=
      Work.Cyl.differentiableAt_pdR (fun r z => Ψ r z t) r z (hΨ t r z hr)
    show DifferentiableAt ℝ
      (fun p : ℝ × ℝ =>
        -(Ψ p.1 p.2 t / p.1) - Work.Cyl.pdR (fun r z => Ψ r z t) p.1 p.2) (r, z)
    fun_prop
  -- The pointwise meridian identity: the residual of the swirl field is `meridianResid • e_θ`.
  have hident : ∀ x : Work.Cyl.R3, ∀ t : ℝ,
      (FiniteTimeSingularity.timeDeriv
          (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
        + FiniteTimeSingularity.directionalDeriv
            (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
            (fun x t => Work.Cyl.cylField
              (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
              (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x) x t)
      = (FiniteTimeSingularity.directionalDeriv
            (fun x t => Work.Cyl.cylField
              (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
              (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x)
            (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
          + (Work.CoreResiduals.meridianResid W Ψ
              (Work.Cyl.radial x) (Work.Cyl.axial x) t) • Work.Cyl.eTheta x) := by
    intro x t
    have hb := vecResid_eq_scalar_smul
      (ur := fun r z t => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
      (uz := fun r z t => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z)
      (W := W) hW (fun t r z hr => ⟨h1 t r z hr, h2 t r z hr⟩) x t
    simpa only [Work.CoreResiduals.meridianResid] using hb
  -- Unfold `VortEqWithDeficit` and substitute the hypotheses `hv`, `hω`.
  have key : Work.CoreResiduals.VortEqWithDeficit P
        (fun x t => WD (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
      ↔ ∀ x : Work.Cyl.R3, ∀ t : ℝ,
          (FiniteTimeSingularity.timeDeriv
              (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
            + FiniteTimeSingularity.directionalDeriv
                (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
                (fun x t => Work.Cyl.cylField
                  (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
                  (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x) x t)
          = (FiniteTimeSingularity.directionalDeriv
                (fun x t => Work.Cyl.cylField
                  (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
                  (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x)
                (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
              + WD (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) := by
    have hbv : (fun x t => Work.LWP.biotSavart
          (fun y => Work.ConstructionInstance.solVort P y t) x)
        = (fun x t => Work.Cyl.cylField
            (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
            (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x) :=
      funext fun x => funext fun t => hv x t
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
