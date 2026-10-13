/-# `Work.CoreResiduals.Enstrophy` — the enstrophy of the constructed vorticity

## What this file is

The delivered residual **R1** is the pointwise statement that the constructed (cut) self-similar
vorticity `solVort P` solves the `ℝ³` vorticity equation

  `∂ₜω + (u·∇)ω = (ω·∇)u`,   `u = BS ω`,

where `ω(x,t) = solVort P x t = λ̄(t)⁻¹·χ(ρ/L)·F(ρ^p/λ̄(t), θ)·e_θ`.

This file computes the **enstrophy** `E(t) = (1/2)∫‖ω(x,t)‖² dx` of the *explicit* field — an
integral that, unlike the velocity, involves no Biot–Savart inversion.  The result is the pointwise
identity, valid for every `x` off the symmetry axis,

  `‖solVort P x t‖² = 4p²·(Γ_p(|θ(x)|)/c_p)²·χ(ρ(x)/L)²·ρ(x)^{2p} / (λ̄(t) + ρ(x)^p)^4`,

which follows from `F_*(z,θ) = p·(Γ_p(θ)/c_p)·2z/(1+z)²` and the algebraic identity

  `λ̄⁻²·(2z/(1+z)²)² = 4ρ^{2p}/(λ̄+ρ^p)^4`   at   `z = ρ^p/λ̄`.

All the `λ̄`-dependence sits in the denominator, which is *strictly increasing* in `λ̄`; the model
enstrophy is therefore *strictly increasing* in `t` (`enstrophy_lt_of_lt`,
`enstrophy_not_constant`).

## What this does *not* give (an important correction)

The enstrophy is **not** a conserved quantity of the `ℝ³` Euler equations: the integrated
vortex-stretching term `∫ω·(ω·∇)u` need not vanish.  This file therefore does **not** refute R1 from
the monotonicity; see `Conservation.lean` for the finding and for the correct invariant (the
energy).  The formal obstructions to R1 proved in this area are `Model.fstar_rate_rigid` and
`ProfileData_T_eq_two`, and the route to a refutation is the elliptic identification of `NOTES.md`
§5.

## Main statements

* `Work.CoreResiduals.enstrophy` — the enstrophy functional; `enstrophyDensity`/`enstrophyDiff` —
  its density and the density difference;
* `Work.CoreResiduals.profile_model_sq` — the squared model profile;
* `Work.CoreResiduals.norm_solVort_sq_model` — the pointwise identity;
* `Work.CoreResiduals.norm_solVort_sq_le` / `norm_solVort_sq_lt` — the pointwise comparison;
* `Work.CoreResiduals.enstrophy_lt_of_lt` — strict monotonicity of the enstrophy in `t`;
* `Work.CoreResiduals.enstrophy_not_constant` — the model enstrophy is not constant.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.Model
import Submission.Work.CoreResiduals.BiotSavart

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## The enstrophy functional -/

/-- **The enstrophy of the constructed vorticity** at time `t`: `E(t) = (1/2)∫‖ω(x,t)‖² dx`.

`E(t) = (1/2)∫‖ω(x,t)‖² dx`.  This is *not* an invariant of the `ℝ³` Euler equations (the
vortex-stretching term contributes, see `Conservation.lean`), but it is an integral of the explicit
field, and `norm_solVort_sq_model` computes its density in closed form. -/
noncomputable def enstrophy {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) (t : ℝ) :
    ℝ :=
  (1 / 2) * ∫ x : R3, ‖solVort P x t‖ ^ 2

theorem enstrophy_apply {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) (t : ℝ) :
    enstrophy P t = (1 / 2) * ∫ x : R3, ‖solVort P x t‖ ^ 2 := rfl

/-- **The enstrophy density** of the constructed vorticity at time `t`, as a function of `x`:
`x ↦ ‖solVort P x t‖²`.  Its integral is twice the enstrophy; it is the object whose pointwise
form is computed by `norm_solVort_sq_model`. -/
noncomputable def enstrophyDensity {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (t : ℝ) : R3 → ℝ :=
  fun x => ‖solVort P x t‖ ^ 2

@[simp] theorem enstrophyDensity_apply {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) (t : ℝ) (x : R3) :
    enstrophyDensity P t x = ‖solVort P x t‖ ^ 2 := rfl

/-- **The difference of the enstrophy densities** at the times `s` and `t`.  Its integral is zero
exactly when the enstrophy is the same at `s` and `t`; the strict positivity of its support is the
positive-measure strictness used in `enstrophy_lt_of_lt`. -/
noncomputable def enstrophyDiff {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (s t : ℝ) : R3 → ℝ :=
  fun x => ‖solVort P x t‖ ^ 2 - ‖solVort P x s‖ ^ 2

@[simp] theorem enstrophyDiff_apply {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) (s t : ℝ) (x : R3) :
    enstrophyDiff P s t x = ‖solVort P x t‖ ^ 2 - ‖solVort P x s‖ ^ 2 := rfl

/-- **The gradient density of the constructed vorticity**: `x ↦ ‖ω(x,t)‖·‖(Dω)(x,t)‖`.  Its
integrability is the hypothesis that makes the integration by parts in the enstrophy conservation
law legal. -/
noncomputable def vortGradDensity {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (t : ℝ) : R3 → ℝ :=
  fun x => ‖solVort P x t‖ * ‖fderiv ℝ (fun y : R3 => solVort P y t) x‖

@[simp] theorem vortGradDensity_apply {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) (t : ℝ) (x : R3) :
    vortGradDensity P t x = ‖solVort P x t‖ * ‖fderiv ℝ (fun y : R3 => solVort P y t) x‖ := rfl

/-- **The vorticity slices of the constructed field are supported in a fixed ball** (the cut-off
makes the box independent of the flow). -/
theorem hasCompactSupport_solVort {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (t : ℝ) : HasCompactSupport (solVort P · t) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : R3) P.R) fun x hx => ?_
  by_contra hne
  exact hx (Work.ConstructionInstance.solVort_supp P t x hne)

/-- The model vorticity vanishes on the symmetry axis (where `e_θ` is the zero vector). -/
theorem solVort_eq_zero_of_radial_eq_zero {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) {x : R3} (h : Work.Cyl.radial x = 0)
    (t : ℝ) : solVort P x t = 0 := by
  have he : Work.Cyl.eTheta x = 0 := by
    rw [Work.Cyl.eTheta, h, one_div, _root_.inv_zero, zero_smul]
  change Work.ConstructionInstance.solVort P x t = 0
  rw [Work.ConstructionInstance.solVort_apply, Work.ConstructionInstance.omegaSz_apply, he,
    smul_zero, smul_zero, smul_zero]

/-! ## The squared model profile -/

/-- **The squared profile of the model data.**  For `g = 0` the profile
`F_{*}(z,θ) = p·(Γ_p(θ)/c_p)·2z/(1+z)²`, oddly extended in `θ`, has square depending on `θ` only
through `|θ|`:

  `profile p 0 z θ ^ 2 = (p·Γ_p(|θ|)/c_p·2z/(1+z)²) ^ 2`.

This is the only place where the odd extension of `profile` is used. -/
theorem profile_model_sq (α : NNReal) (z θ : ℝ) :
    (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α)
        (fun _ _ => (0 : ℝ)) z θ) ^ 2
      = (Work.ConstructionInstance.profExp α
          * (Work.Spaces.Gam (Work.ConstructionInstance.profExp α) |θ| / Work.Spaces.c
              (Work.ConstructionInstance.profExp α)) * Work.FM.Fstar z) ^ 2 := by
  by_cases h : 0 ≤ θ
  · rw [Work.ConstructionInstance.profile_of_nonneg h, abs_of_nonneg h, add_zero,
      Work.Construction.Fstar]
  · rw [Work.ConstructionInstance.profile_of_neg h, abs_of_neg (not_le.mp h), add_zero,
      Work.Construction.Fstar, neg_sq]

/-- **The algebraic kernel of the pointwise identity**:
`λ̄⁻²·(2z/(1+z)²)² = 4ρ^{2p}/(λ̄+ρ^p)^4` for `z = ρ^p/λ̄`, `λ̄ > 0`, `ρ > 0`. -/
theorem key_algebra (lam ρ p : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) :
    (lam⁻¹) ^ 2 * (2 * (ρ ^ p / lam) / (1 + ρ ^ p / lam) ^ 2) ^ 2
      = 4 * ρ ^ (2 * p) / (lam + ρ ^ p) ^ 4 := by
  have hu : 0 < ρ ^ p := Real.rpow_pos_of_pos hρ p
  have hsq : ρ ^ (2 * p) = (ρ ^ p) ^ 2 := by
    rw [mul_comm (2 : ℝ) p, Real.rpow_mul (le_of_lt hρ) p 2, Real.rpow_two]
  rw [hsq]
  have h2 : (1 + ρ ^ p / lam) = (lam + ρ ^ p) / lam := by field_simp
  rw [h2]
  field_simp
  norm_num


/-- **The enstrophy density of the model data in closed form**: the product of the algebraic
kernel `key_algebra` with the constant angular/radial factors. -/
theorem enstrophy_density_model (lam ρ p g χ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) :
    lam⁻¹ ^ 2 * χ ^ 2 * (p * g * (2 * (ρ ^ p / lam) / (1 + ρ ^ p / lam) ^ 2)) ^ 2
      = 4 * p ^ 2 * g ^ 2 * χ ^ 2 * ρ ^ (2 * p) / (lam + ρ ^ p) ^ 4 := by
  have hkey := key_algebra lam ρ p hlam hρ
  calc lam⁻¹ ^ 2 * χ ^ 2 * (p * g * (2 * (ρ ^ p / lam) / (1 + ρ ^ p / lam) ^ 2)) ^ 2
      = (p * g) ^ 2 * χ ^ 2 * (lam⁻¹ ^ 2 * (2 * (ρ ^ p / lam) / (1 + ρ ^ p / lam) ^ 2) ^ 2) := by
        ring
    _ = (p * g) ^ 2 * χ ^ 2 * (4 * ρ ^ (2 * p) / (lam + ρ ^ p) ^ 4) := by rw [hkey]
    _ = 4 * p ^ 2 * g ^ 2 * χ ^ 2 * ρ ^ (2 * p) / (lam + ρ ^ p) ^ 4 := by ring

/-! ## The pointwise identity for the model vorticity -/

/-- **The pointwise form of the model enstrophy.**  Off the symmetry axis (`r ≠ 0`), the squared
norm of the constructed vorticity at time `t` is

  `4p²·(Γ_p(|θ|)/c_p)²·χ(ρ/L)²·ρ^{2p} / (λ̄ + ρ^p)^4`,

in which the **only** dependence on the modulation `λ̄` is through the denominator.  Consequently the
enstrophy density is strictly decreasing in `λ̄` wherever the field does not vanish. -/
theorem norm_solVort_sq_model {α : NNReal} (I : Inhabitant α) (x : R3) (t : ℝ)
    (hlam : 0 < I.P.lam t) (hr : Work.Cyl.radial x ≠ 0) :
    ‖solVort I.P x t‖ ^ 2
      = 4 * (Work.ConstructionInstance.profExp α) ^ 2
          * (Work.Spaces.Gam (Work.ConstructionInstance.profExp α) |Work.Cyl.theta x|
              / Work.Spaces.c (Work.ConstructionInstance.profExp α)) ^ 2
          * (Work.Stability.chi (Work.Cyl.rho x / I.P.L)) ^ 2
          * (Work.Cyl.rho x) ^ (2 * Work.ConstructionInstance.profExp α)
            / (I.P.lam t + (Work.Cyl.rho x) ^ (Work.ConstructionInstance.profExp α)) ^ 4 := by
  have hρ : 0 < Work.Cyl.rho x := by
    rw [Work.Cyl.rho_eq_norm]
    refine norm_pos_iff.mpr fun hx => hr ?_
    rw [hx]
    simp [Work.Cyl.radial, Work.Cyl.radSq]
  have hlhs : ‖solVort I.P x t‖ ^ 2
      = (I.P.lam t)⁻¹ ^ 2 * (Work.Stability.chi (Work.Cyl.rho x / I.P.L)) ^ 2
          * (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α)
              (fun _ _ => (0 : ℝ))
              (Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / I.P.lam t)
              (Work.Cyl.theta x)) ^ 2 := by
    change ‖Work.ConstructionInstance.solVort I.P x t‖ ^ 2 = _
    rw [Work.ConstructionInstance.solVort_apply, Work.ConstructionInstance.omegaSz_apply, I.hg,
      norm_smul, norm_smul, norm_smul, Work.Cyl.norm_eTheta x hr, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hlam), abs_of_nonneg (Work.Stability.chi_nonneg _)]
    rw [mul_pow, mul_pow, sq_abs]
    ring
  rw [hlhs, profile_model_sq α (Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / I.P.lam t)
      (Work.Cyl.theta x), Work.FM.Fstar,
    enstrophy_density_model (I.P.lam t) (Work.Cyl.rho x) (Work.ConstructionInstance.profExp α)
      (Work.Spaces.Gam (Work.ConstructionInstance.profExp α) |Work.Cyl.theta x|
        / Work.Spaces.c (Work.ConstructionInstance.profExp α))
      (Work.Stability.chi (Work.Cyl.rho x / I.P.L)) hlam hρ]

/-- `ρ(x) > 0` whenever `x` is off the symmetry axis. -/
theorem rho_pos_of_radial_ne_zero {x : R3} (hr : Work.Cyl.radial x ≠ 0) : 0 < Work.Cyl.rho x := by
  rw [Work.Cyl.rho_eq_norm]
  refine norm_pos_iff.mpr fun hx => hr ?_
  rw [hx]
  simp [Work.Cyl.radial, Work.Cyl.radSq]

/-- **The pointwise comparison of the enstrophy densities**: a smaller modulation means a larger
density.  This is the pointwise core of the strict monotonicity of the enstrophy in `t`. -/
theorem norm_solVort_sq_le {α : NNReal} (I : Inhabitant α) (x : R3) {t₁ t₂ : ℝ}
    (h₁ : 0 < I.P.lam t₁) (h₂ : 0 < I.P.lam t₂) (h : I.P.lam t₂ ≤ I.P.lam t₁) :
    ‖solVort I.P x t₁‖ ^ 2 ≤ ‖solVort I.P x t₂‖ ^ 2 := by
  by_cases hr : Work.Cyl.radial x = 0
  · rw [solVort_eq_zero_of_radial_eq_zero I.P hr t₁,
      solVort_eq_zero_of_radial_eq_zero I.P hr t₂]
  · rw [norm_solVort_sq_model I x t₁ h₁ hr, norm_solVort_sq_model I x t₂ h₂ hr]
    have hρ : 0 < Work.Cyl.rho x := rho_pos_of_radial_ne_zero hr
    have hu : 0 < Work.Cyl.rho x ^ (Work.ConstructionInstance.profExp α) :=
      Real.rpow_pos_of_pos hρ _
    have hA : 0 ≤ 4 * (Work.ConstructionInstance.profExp α) ^ 2
        * (Work.Spaces.Gam (Work.ConstructionInstance.profExp α) |Work.Cyl.theta x|
            / Work.Spaces.c (Work.ConstructionInstance.profExp α)) ^ 2
        * (Work.Stability.chi (Work.Cyl.rho x / I.P.L)) ^ 2
        * (Work.Cyl.rho x) ^ (2 * Work.ConstructionInstance.profExp α) := by positivity
    have hDle : (I.P.lam t₂ + Work.Cyl.rho x ^ (Work.ConstructionInstance.profExp α)) ^ 4
        ≤ (I.P.lam t₁ + Work.Cyl.rho x ^ (Work.ConstructionInstance.profExp α)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    exact div_le_div_of_nonneg_left hA (by positivity) hDle

/-- **The strict pointwise comparison**, on the set where the field does not vanish. -/
theorem norm_solVort_sq_lt {α : NNReal} (I : Inhabitant α) (x : R3) {t₁ t₂ : ℝ}
    (h₁ : 0 < I.P.lam t₁) (h₂ : 0 < I.P.lam t₂) (h : I.P.lam t₂ < I.P.lam t₁)
    (hr : Work.Cyl.radial x ≠ 0) (hχ : 0 < Work.Stability.chi (Work.Cyl.rho x / I.P.L))
    (hG : 0 < Work.Spaces.Gam (Work.ConstructionInstance.profExp α) |Work.Cyl.theta x|) :
    ‖solVort I.P x t₁‖ ^ 2 < ‖solVort I.P x t₂‖ ^ 2 := by
  rw [norm_solVort_sq_model I x t₁ h₁ hr, norm_solVort_sq_model I x t₂ h₂ hr]
  have hρ : 0 < Work.Cyl.rho x := rho_pos_of_radial_ne_zero hr
  have hu : 0 < Work.Cyl.rho x ^ (Work.ConstructionInstance.profExp α) :=
    Real.rpow_pos_of_pos hρ _
  have hA : 0 < 4 * (Work.ConstructionInstance.profExp α) ^ 2
      * (Work.Spaces.Gam (Work.ConstructionInstance.profExp α) |Work.Cyl.theta x|
          / Work.Spaces.c (Work.ConstructionInstance.profExp α)) ^ 2
      * (Work.Stability.chi (Work.Cyl.rho x / I.P.L)) ^ 2
      * (Work.Cyl.rho x) ^ (2 * Work.ConstructionInstance.profExp α) := by
    have hc : 0 < Work.Spaces.c (Work.ConstructionInstance.profExp α) :=
      lt_of_lt_of_le (by norm_num) (Work.Spaces.c_bounds _
        (Work.ConstructionInstance.profExp_pos I.P.hα)
        (by rw [Work.ConstructionInstance.profExp]; linarith [I.P.hα13])).1
    have h1 : 0 < Work.ConstructionInstance.profExp α := Work.ConstructionInstance.profExp_pos I.P.hα
    have h2 : 0 < Work.Spaces.Gam (Work.ConstructionInstance.profExp α) |Work.Cyl.theta x|
        / Work.Spaces.c (Work.ConstructionInstance.profExp α) := div_pos hG hc
    have h3 : 0 < (Work.Cyl.rho x) ^ (2 * Work.ConstructionInstance.profExp α) :=
      Real.rpow_pos_of_pos hρ _
    positivity
  have hDlt : (I.P.lam t₂ + Work.Cyl.rho x ^ (Work.ConstructionInstance.profExp α)) ^ 4
      < (I.P.lam t₁ + Work.Cyl.rho x ^ (Work.ConstructionInstance.profExp α)) ^ 4 :=
    pow_lt_pow_left₀ (by linarith) (by positivity) (by norm_num)
  exact div_lt_div_of_pos_left hA (by positivity) hDlt

/-! ## Strict monotonicity of the enstrophy, and its non-constancy

The two analytic side conditions of this section are *positive-measure strictness* of the pointwise
comparison and *integrability* of the enstrophy density; both are proved for the model data in the
delegated lemmas `Work.CoreResiduals.strict_pos_set_enstrophy` and
`Work.CoreResiduals.integrable_norm_solVort_sq`.  Keeping them as hypotheses here isolates the
*pointwise* content of the finding, which is what the file proves outright. -/

/-- **The strict monotonicity of the model enstrophy.**  For `0 ≤ t₁ < t₂ < T = 2` the enstrophy is
strictly larger at `t₂`: the only `t`-dependence of the density is the strictly increasing
denominator `(λ̄(t) + ρ^p)^4`.  (This is *not* an obstruction to R1 — the enstrophy is not conserved
in `ℝ³`; see `Conservation.lean`.) -/
theorem enstrophy_lt_of_lt {α : NNReal} (I : Inhabitant α) {t₁ t₂ : ℝ}
    (h₁ : t₁ ∈ Set.Ico 0 I.P.T) (h₂ : t₂ ∈ Set.Ico 0 I.P.T) (h : t₁ < t₂)
    (hint₁ : Integrable (fun x : R3 => ‖solVort I.P x t₁‖ ^ 2))
    (hint₂ : Integrable (fun x : R3 => ‖solVort I.P x t₂‖ ^ 2))
    (hstrict : 0 < volume (Function.support fun x : R3 =>
      ‖solVort I.P x t₂‖ ^ 2 - ‖solVort I.P x t₁‖ ^ 2)) :
    enstrophy I.P t₁ < enstrophy I.P t₂ := by
  have hl₁ : 0 < I.P.lam t₁ := I.P.hlam t₁ ⟨by linarith [h₁.1], h₁.2⟩
  have hl₂ : 0 < I.P.lam t₂ := I.P.hlam t₂ ⟨by linarith [h₂.1], h₂.2⟩
  have hlt : I.P.lam t₂ ≤ I.P.lam t₁ := by rw [I.hlam t₁, I.hlam t₂]; linarith
  have hnonneg : 0 ≤ᵐ[volume] fun x : R3 =>
      ‖solVort I.P x t₂‖ ^ 2 - ‖solVort I.P x t₁‖ ^ 2 :=
    Filter.Eventually.of_forall fun x => sub_nonneg.mpr (norm_solVort_sq_le I x hl₁ hl₂ hlt)
  have hint : Integrable fun x : R3 => ‖solVort I.P x t₂‖ ^ 2 - ‖solVort I.P x t₁‖ ^ 2 :=
    hint₂.sub hint₁
  have hdiff : 0 < ∫ x : R3, (‖solVort I.P x t₂‖ ^ 2 - ‖solVort I.P x t₁‖ ^ 2) :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hnonneg hint).mpr hstrict
  have hsub : (∫ x : R3, (‖solVort I.P x t₂‖ ^ 2 - ‖solVort I.P x t₁‖ ^ 2))
      = (∫ x : R3, ‖solVort I.P x t₂‖ ^ 2) - ∫ x : R3, ‖solVort I.P x t₁‖ ^ 2 :=
    integral_sub hint₂ hint₁
  rw [hsub] at hdiff
  rw [enstrophy_apply, enstrophy_apply]
  linarith

/-- **The model enstrophy is not constant on `[0, T)`.** -/
theorem enstrophy_not_constant {α : NNReal} (I : Inhabitant α)
    (hint : ∀ t ∈ Set.Ico 0 I.P.T, Integrable (fun x : R3 => ‖solVort I.P x t‖ ^ 2))
    (hstrict : 0 < volume (Function.support fun x : R3 =>
      ‖solVort I.P x 1‖ ^ 2 - ‖solVort I.P x 0‖ ^ 2)) :
    ∃ t₁ ∈ Set.Ico 0 I.P.T, ∃ t₂ ∈ Set.Ico 0 I.P.T, enstrophy I.P t₁ ≠ enstrophy I.P t₂ := by
  have h0 : (0 : ℝ) ∈ Set.Ico 0 I.P.T := ⟨le_refl 0, by rw [I.hT]; norm_num⟩
  have h1 : (1 : ℝ) ∈ Set.Ico 0 I.P.T := ⟨by norm_num, by rw [I.hT]; norm_num⟩
  exact ⟨0, h0, 1, h1, ne_of_lt (enstrophy_lt_of_lt I h0 h1 (by norm_num) (hint 0 h0)
    (hint 1 h1) hstrict)⟩
