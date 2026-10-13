/-
# `Work.R1G` — the R1 **G-route**: the modulated profile data and the deficit cancellation

This area implements the *honest* route to residual **R1** of the Elgindi finite-time-singularity
formalisation, as recommended by `Submission/Work/CoreResiduals/NOTES.md` §13 (and the final report
§2): the zero-deficit residual `VortEq α P` (the `ℝ³` vorticity equation for `u = BS(solVort P)`)
**fails** at every delivered `ProfileData` — the `St1` cut-off `χ(ρ/L)` is not a function of the
self-similar variable `ρ^p/λ̄`, so the cut field is genuinely non-self-similar and the non-local
Biot–Savart velocity cannot cancel the profile terms — while the *honest* interface carries the
deficit explicitly (`Defs.VortEqWithDeficit`) with the **modulation `g ≠ 0`** that cancels it
(`Work.Stability.GEquationFar`, whose right-hand side `gDynRHS` is explicit).

## The three deliverables of the area (see `NOTES.md` for the stage report)

1. **the modulated profile data** (`ModulatedData`): the Construction area's reference profile
   `F_*` together with a *nonzero* perturbation `g` whose equation is the `St2`/`St3` `g`-equation
   `Work.Stability.GEquationFar` — the **promotion** of the *reduced* identity
   `Work.Construction.Fstar_stationary_identity` to the full profile equation at the effective rate
   (`GEquationPromotion.dynEq_of_gEquation`: the converse of the Stability layer's `DynGEquation`);
2. **the deficit cancellation** (`gEqResidual_eq`, `meridianResid_cut_ssVort`): the meridian
   residual of the constructed (cut) field is an *explicit* function — the (χ-weighted) profile-level
   `g`-equation residual plus the explicit cut-off term `(χ'(ρ/L)/L)·K·W₀`.  Consequently the
   `g`-equation cancels everything except the cut-off term, which is `r1Deficit` in meridian form;
3. **the `hR1`-free check** (`Check.theorem1_of_model_data_honest`,
   `Check.check_theorem_1_of_inputs_of_fixed_honest`): the end-to-end chain of
   `Work.CoreResiduals.Check` with `VortEq` replaced by the deficit form
   (`CoreResiduals.vortEq_iff_noDeficit` makes the substitution mechanical).

## What this module fixes

The vocabulary: the profile `F = F_* + P.g` of a `ProfileData`, the **uncut** self-similar
vorticity and its cut-off decomposition, the meridian point and the meridian slice of the
constructed field, the modulation state at the **effective rate** `2·(-λ̄')` of the *physical*
vorticity equation (`Work.CoreResiduals.Model.model_rate_physical_eq_reference`), the profile
equation at the effective rate, the meridian residual identity, and the G-route's honest residual.

## Conventions

* `p = profExp α = 3α` is the profile exponent of the ansatz (`ρ^p`); `α` is the Hölder exponent of
  the challenge.  Every statement about the profile is stated for the `UVR` operator with parameter
  `p`, and the elliptic law is `Work.Elliptic.bslOp p Φ = F`.
* The self-similar pair is `ssVort p λ F`, `ssPsi p λ Φ` of `Work.CoreResiduals.SelfSimReduction`,
  i.e. `W(r,z,t) = λ(t)⁻¹F(ρ(r,z)^p/λ(t), Θ(r,z))` and `ψ(r,z,t) = ρ(r,z)²λ(t)⁻¹Φ(ρ^p/λ(t),Θ)`.
* `meridianResid W ψ` is the residual
  `∂ₜW + (∂_zψ)∂_rW + (-(ψ/r) - ∂_rψ)∂_zW - ((∂_zψ)/r)W`, and the `ℝ³` vorticity equation for
  `u = psiField ψ`, `ω = W·e_θ` is equivalent to `meridianResid W ψ = 0`
  (`Work.CoreResiduals.VorticityEquation.vorticityEquation_psiField_iff_scalar`).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.Stability.ModEqn
import Submission.Work.Stability.Cutoff
import Submission.Work.CoreResiduals.VorticityEquation
import Submission.Work.CoreResiduals.R1Status
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.ConstructionInstance.Patch

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.R1G

variable {α : NNReal}

/-- `ℝ³`, definitionally `Work.ConstructionInstance.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The profile exponent of a `ProfileData` satisfies `0 < p`. -/
theorem profExp_pos_of_data (P : Work.ConstructionInstance.ProfileData α) :
    0 < Work.ConstructionInstance.profExp α :=
  Work.ConstructionInstance.profExp_pos P.hα

/-- **The profile exponent of a `ProfileData` lies in `(0,1]`** — the range in which the
Construction/Stability identities (`Work.Construction.Fstar_stationary_identity`,
`Work.Stability.DynGEquation`) hold.  The challenge's `α ≤ 1/3` is exactly what makes `p = 3α ≤ 1`. -/
theorem profExp_le_one (P : Work.ConstructionInstance.ProfileData α) :
    Work.ConstructionInstance.profExp α ≤ 1 := by
  have h := P.hα13
  rw [Work.ConstructionInstance.profExp]
  linarith

/-! ## The full profile `F = F_* + g` -/

/-- **The full profile** `F = F_* + g` of a `ProfileData`, as a function of the self-similar
variables `(z,θ)`: the Construction area's reference profile `Work.Construction.Fstar (profExp α)`
plus the delivered perturbation `P.g`. -/
def profOf (P : Work.ConstructionInstance.ProfileData α) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Fstar (Work.ConstructionInstance.profExp α) z θ + P.g z θ

theorem profOf_apply (P : Work.ConstructionInstance.ProfileData α) (z θ : ℝ) :
    profOf P z θ = Work.Construction.Fstar (Work.ConstructionInstance.profExp α) z θ + P.g z θ :=
  rfl

/-- **The perturbation as a family** (`Work.Stability.F3`): the delivered interface's perturbation
`P.g` is *stationary* (it does not depend on the self-similar time `s`).  This is the bridge to the
`St2`/`St3` vocabulary, where the modulation is a family `(z,θ,s) ↦ g(z,θ,s)`. -/
def gOf3 (P : Work.ConstructionInstance.ProfileData α) : Work.Stability.F3 :=
  fun z θ _ => P.g z θ

theorem gOf3_apply (P : Work.ConstructionInstance.ProfileData α) (z θ s : ℝ) :
    gOf3 P z θ s = P.g z θ := rfl

/-- **The full profile as a family**: `F_* + g` read in the `St2`/`St3` vocabulary. -/
def profOf3 (P : Work.ConstructionInstance.ProfileData α) : Work.Stability.F3 :=
  fun z θ _ => profOf P z θ

/-- `profOf3` is the Stability layer's `Ftot α (gOf3 P)`. -/
theorem profOf3_eq_Ftot (P : Work.ConstructionInstance.ProfileData α) :
    profOf3 P = fun z θ s =>
      Work.Stability.Ftot (Work.ConstructionInstance.profExp α) (gOf3 P) s z θ := by
  funext z θ s
  simp only [profOf3, Work.Stability.Ftot, gOf3, profOf]

/-- The profile at `θ ≥ 0` is the `profile` used by the explicit constructed vorticity. -/
theorem profile_eq_profOf (P : Work.ConstructionInstance.ProfileData α) {z θ : ℝ} (hθ : 0 ≤ θ) :
    Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g z θ
      = profOf P z θ := by
  rw [Work.ConstructionInstance.profile_of_nonneg hθ, profOf]

/-! ## The uncut field and the cut-off decomposition -/

/-- **The uncut self-similar vorticity** of a `ProfileData`:
`ω(x,t) = λ̄(t)⁻¹·F(ρ(x)^p/λ̄(t), θ(x))·e_θ(x)` with `F = F_* + P.g`.  This is the field the
`g`-equation (and the meridian equation) is about; the constructed field `solVort P` is its radial
cut-off. -/
def uncutVort (P : Work.ConstructionInstance.ProfileData α) : R3 → ℝ → R3 :=
  fun x t => (P.lam t)⁻¹ •
    Work.ConstructionInstance.omegaSz (Work.ConstructionInstance.profExp α) P.g
      (Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / P.lam t) x

theorem uncutVort_apply (P : Work.ConstructionInstance.ProfileData α) (x : R3) (t : ℝ) :
    uncutVort P x t = (P.lam t)⁻¹ •
      Work.ConstructionInstance.omegaSz (Work.ConstructionInstance.profExp α) P.g
        (Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / P.lam t) x := rfl

/-- **The cut-off decomposition of the constructed vorticity**:
`solVort P = χ(ρ(·)/L) • uncutVort P`.  This is the exact structural fact behind the finding that
the zero-deficit residual cannot hold: the cut-off factor is *not* a function of the self-similar
variable, so `solVort P` differs from the self-similar field on the annulus `L < ρ < 2L`. -/
theorem solVort_eq_cut_smul (P : Work.ConstructionInstance.ProfileData α) :
    Work.ConstructionInstance.solVort P
      = fun x t => Work.Stability.chi (Work.Cyl.rho x / P.L) • uncutVort P x t := by
  funext x t
  rw [Work.ConstructionInstance.solVort_apply, uncutVort_apply, smul_smul, smul_smul,
    mul_comm]

/-- The constructed vorticity is the cut-off of the uncut one, pointwise. -/
theorem solVort_apply_eq (P : Work.ConstructionInstance.ProfileData α) (x : R3) (t : ℝ) :
    Work.ConstructionInstance.solVort P x t
      = Work.Stability.chi (Work.Cyl.rho x / P.L) • uncutVort P x t :=
  congrFun (congrFun (solVort_eq_cut_smul P) x) t

/-! ## The meridian point and the meridian slice -/

/-- **The meridian point** `(r, 0, z) ∈ ℝ³`: the half-plane `x₁ = 0` on which the axisymmetric
fields are represented by their `(r, z)`-profiles.  For `r > 0` this is off the axis, so the
cylindrical frame is regular there. -/
def mkPt (r z : ℝ) : R3 := !₂[r, 0, z]

@[simp] theorem mkPt_apply_zero (r z : ℝ) : mkPt r z 0 = r := rfl
@[simp] theorem mkPt_apply_one (r z : ℝ) : mkPt r z 1 = 0 := rfl
@[simp] theorem mkPt_apply_two (r z : ℝ) : mkPt r z 2 = z := rfl

theorem radial_mkPt (r z : ℝ) : Work.Cyl.radial (mkPt r z) = |r| := by
  rw [Work.Cyl.radial, Work.Cyl.radSq, mkPt_apply_zero, mkPt_apply_one]
  have : r ^ 2 + 0 ^ 2 = r ^ 2 := by ring
  rw [this, Real.sqrt_sq_eq_abs]

theorem axial_mkPt (r z : ℝ) : Work.Cyl.axial (mkPt r z) = z := rfl

theorem rho_mkPt (r z : ℝ) :
    Work.Cyl.rho (mkPt r z) = Work.Cyl.rhoP r z := by
  simp [Work.Cyl.rho, Work.Cyl.rhoP, Work.Cyl.radSq, Work.Cyl.axial, mkPt]

/-- The `ℝ³` radial coordinate is the meridian `rhoP` of `(radial, axial)`. -/
theorem rho_eq_rhoP (x : R3) :
    Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
  rw [Work.Cyl.rho, Work.Cyl.rhoP]
  congr 1
  rw [Work.Cyl.radial_sq]

/-- The `ℝ³` polar angle is the meridian `thetaP` of `(radial, axial)`. -/
theorem theta_eq_thetaP (x : R3) :
    Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl

theorem theta_mkPt {r : ℝ} (hr : 0 < r) (z : ℝ) :
    Work.Cyl.theta (mkPt r z) = Work.Cyl.thetaP r z := by
  rw [Work.Cyl.theta, Work.Cyl.thetaP, axial_mkPt, radial_mkPt, abs_of_pos hr]

/-- The angular vector at the meridian point `(r,0,z)` is the second standard basis vector
`e_θ = e₁`. -/
theorem eTheta_mkPt {r : ℝ} (hr : 0 < r) (z : ℝ) :
    Work.Cyl.eTheta (mkPt r z) = (FiniteTimeSingularity.e 1 : R3) := by
  rw [Work.Cyl.eTheta, Work.Cyl.angularVec, radial_mkPt, abs_of_pos hr, mkPt_apply_zero,
    mkPt_apply_one]
  ext i
  fin_cases i <;>
    simp [FiniteTimeSingularity.e, inv_mul_eq_div, div_self (ne_of_gt hr)]

/-! ## The modulation rate, and the profile equation at the effective rate -/

/-- **The modulation rate**: `κ` with `λ̄'(t) = -κ` on the pre-window.  This is the design's
`κ = -λ̄'` (`Work.Stability.Defs`), the rate in the paper's *dilated* time; the rate entering the
*physical* profile equation of residual R1 is `2κ` (`Model.model_rate_physical`). -/
def EffRate (P : Work.ConstructionInstance.ProfileData α) (κ : ℝ) : Prop :=
  ∀ t ∈ Work.ConstructionInstance.preWindow P.T, HasDerivAt P.lam (-κ) t

/-- **The profile equation at the effective rate** `2κ`: the constant-rate rescaled vorticity
equation (`Work.CoreResiduals.DynEqConst`) for the full profile `F = F_* + P.g`, at the *physical*
effective rate `2·(-λ̄')` and the reference space rate `b = 1`.  At the inhabitant the effective rate
is `1 = κ*` (`Work.CoreResiduals.model_rate_physical_eq_reference`), so this is the *reference*
profile equation — the equation `Work.Construction.Fstar_stationary_identity` is a reduction of. -/
def ProfileEq (P : Work.ConstructionInstance.ProfileData α) (κ : ℝ) (Φ : ℝ → ℝ → ℝ) : Prop :=
  Work.CoreResiduals.DynEqConst (Work.ConstructionInstance.profExp α) (2 * κ) 1 (profOf P) Φ

/-- **The profile-level residual** of the G-route: the left-hand side of the profile equation at the
effective rate `2κ`, i.e. `2κ·(F + D_zF) + UVR p F Φ` with `F = F_* + P.g`; its vanishing on the
open quadrant is `ProfileEq`. -/
def profileResidGen (p κ : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * κ * (F z θ + Work.Spaces.Dz F z θ)
    + Work.Construction.UVR p F Φ z θ

theorem profileResidGen_apply (p κ : ℝ) (F Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    profileResidGen p κ F Φ z θ
      = 2 * κ * (F z θ + Work.Spaces.Dz F z θ) + Work.Construction.UVR p F Φ z θ := rfl

/-- The profile residual of a `ProfileData` at the effective rate `2κ`. -/
def profileResid (P : Work.ConstructionInstance.ProfileData α) (κ : ℝ) (Φ : ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ :=
  profileResidGen (Work.ConstructionInstance.profExp α) κ (profOf P) Φ

theorem profileResid_apply (P : Work.ConstructionInstance.ProfileData α) (κ : ℝ)
    (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    profileResid P κ Φ z θ
      = 2 * κ * (profOf P z θ + Work.Spaces.Dz (profOf P) z θ)
        + Work.Construction.UVR (Work.ConstructionInstance.profExp α) (profOf P) Φ z θ := rfl

/-- `ProfileEq` is the vanishing of the profile residual on the open quadrant. -/
theorem profileEq_iff (P : Work.ConstructionInstance.ProfileData α) (κ : ℝ) (Φ : ℝ → ℝ → ℝ) :
    ProfileEq P κ Φ
      ↔ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → profileResid P κ Φ z θ = 0 := by
  rw [ProfileEq, Work.CoreResiduals.DynEqConst]
  constructor
  · intro h z θ hzθ
    rw [profileResid_apply]
    linarith [h z θ hzθ]
  · intro h z θ hzθ
    have h1 := h z θ hzθ
    rw [profileResid_apply] at h1
    linarith [h1]

/-! ## The meridian pair of a `ProfileData` -/

/-- **The self-similar meridian pair of a `ProfileData`**: the vorticity profile `W` of the *uncut*
field, in the self-similar variables, i.e. `Work.CoreResiduals.ssVort` at the profile `F = F_* + g`. -/
def ssVortOf (P : Work.ConstructionInstance.ProfileData α) : ℝ → ℝ → ℝ → ℝ :=
  Work.CoreResiduals.ssVort (Work.ConstructionInstance.profExp α) P.lam (profOf P)

/-- The self-similar stream function of a `ProfileData` at a profile `Φ`. -/
def ssPsiOf (P : Work.ConstructionInstance.ProfileData α) (Φ : ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ → ℝ :=
  Work.CoreResiduals.ssPsi (Work.ConstructionInstance.profExp α) P.lam Φ

/-- **The meridian slice of the uncut field**: at the meridian point `(r,0,z)` with `r > 0`, `z ≥ 0`
the uncut vorticity is `ssVort` times `e_θ`. -/
theorem uncutVort_mkPt {P : Work.ConstructionInstance.ProfileData α} {r z : ℝ}
    (hr : 0 < r) (hz : 0 ≤ z) (t : ℝ) :
    uncutVort P (mkPt r z) t
      = ssVortOf P r z t • Work.Cyl.eTheta (mkPt r z) := by
  have hθ : 0 ≤ Work.Cyl.thetaP r z := by
    rw [Work.Cyl.thetaP]
    exact Real.arctan_nonneg.mpr (div_nonneg hz (le_of_lt hr))
  rw [uncutVort_apply, ssVortOf, Work.CoreResiduals.ssVort,
    Work.ConstructionInstance.omegaSz_apply, rho_mkPt, theta_mkPt hr,
    Work.ConstructionInstance.profile_of_nonneg hθ, profOf, smul_smul]

/-- **The uncut field is `ssVort·e_θ` in the meridian plane.**  Together with
`Work.CoreResiduals.VorticityEquation.vorticityEquation_psiField_iff_scalar` this is the bridge
from the profile-level analysis to the `ℝ³` equation. -/
theorem uncutVort_mkPt_eq {P : Work.ConstructionInstance.ProfileData α} {r z : ℝ}
    (hr : 0 < r) (hz : 0 ≤ z) (t : ℝ) :
    uncutVort P (mkPt r z) t
      = (Work.CoreResiduals.ssVort (Work.ConstructionInstance.profExp α) P.lam (profOf P) r z t)
        • Work.Cyl.eTheta (mkPt r z) :=
  uncutVort_mkPt hr hz t


/-! ## The modulation state at the effective rate, and the `g`-equation of the delivered data -/

/-- **The modulation state of the delivered data at the effective rate `2κ`**: the amplitude rate
is the *physical* effective rate `2κ` (twice the paper's dilated-time rate `κ = -λ̄'`, see
`Work.CoreResiduals.Model`) and the space rate is the reference `b = 1` (forced by
`Work.CoreResiduals.ProfileData_T_eq_two`). -/
def modStateOf (κ : ℝ) : Work.Stability.ModState :=
  { kappa := fun _ => 2 * κ, b := fun _ => 1 }

@[simp] theorem modStateOf_kappa (κ s : ℝ) : (modStateOf κ).kappa s = 2 * κ := rfl
@[simp] theorem modStateOf_b (κ s : ℝ) : (modStateOf κ).b s = 1 := rfl

/-- **The stream function as a family** (`Work.Stability.F3`): the delivered data's stream function
is stationary. -/
def phiOf3 (Φ : ℝ → ℝ → ℝ) : Work.Stability.F3 := fun z θ _ => Φ z θ

@[simp] theorem phiOf3_apply (Φ : ℝ → ℝ → ℝ) (z θ s : ℝ) : phiOf3 Φ z θ s = Φ z θ := rfl

/-- **The far-field term as a family** (`Work.Stability.F3`). -/
def farOf3 (Far : ℝ → ℝ → ℝ) : Work.Stability.F3 := fun z θ _ => Far z θ

@[simp] theorem farOf3_apply (Far : ℝ → ℝ → ℝ) (z θ s : ℝ) : farOf3 Far z θ s = Far z θ := rfl

/-- **The `g`-equation of the delivered data, at the effective rate, with the far-field deficit**
(the `St2`/`St3` equation `Work.Stability.GEquationFar` at the modulation state `modStateOf κ`, the
stationary perturbation `gOf3 P`, the stationary stream function `phiOf3 Φ` and the deficit
`farOf3 Far`):

  `κ_s ∂_s g + 𝓛_Γ^T(g) = gDynRHS + Far`  with `gDynRHS = Work.Stability.gDynRHS` **explicit**.

This is the *profile-level* equation the honest modulation solves; the zero-deficit form
`Far = 0` is `Work.Stability.GEquation`. -/
def GEquationStat (P : Work.ConstructionInstance.ProfileData α) (κ : ℝ) (Φ : ℝ → ℝ → ℝ)
    (Far : ℝ → ℝ → ℝ) : Prop :=
  Work.Stability.GEquationFar (Work.ConstructionInstance.profExp α) (modStateOf κ)
    (gOf3 P) (phiOf3 Φ) (farOf3 Far)

/-- **The `g`-equation residual** of the delivered data at the effective rate `2κ`: the profile-level
quantity `𝓛_Γ^T(g) - gDynRHS` whose vanishing (up to `Far`) is the `g`-equation.  Because the
delivered perturbation `P.g` is *stationary*, the `∂_s g`-term of the `g`-equation drops out. -/
def gEqResidual (P : Work.ConstructionInstance.ProfileData α) (κ : ℝ) (Φ : ℝ → ℝ → ℝ)
    (z θ : ℝ) : ℝ :=
  Work.Coercivity.LGammaT (Work.ConstructionInstance.profExp α) P.g z θ
    - Work.Stability.gDynRHS (Work.ConstructionInstance.profExp α) (modStateOf κ) (gOf3 P)
        (phiOf3 Φ) z θ 0

/-- The `s`-slice of the stationary perturbation is the perturbation itself. -/
theorem slice_gOf3 (P : Work.ConstructionInstance.ProfileData α) (s : ℝ) :
    Work.Stability.slice (gOf3 P) s = P.g := rfl

/-- The stationary perturbation has vanishing self-similar-time derivative. -/
theorem deriv_gOf3 (P : Work.ConstructionInstance.ProfileData α) (z θ s : ℝ) :
    deriv (fun u : ℝ => gOf3 P z θ u) s = 0 := by
  have : (fun u : ℝ => gOf3 P z θ u) = fun _ : ℝ => P.g z θ := by
    funext u; rw [gOf3_apply]
  rw [this, deriv_const]

/-- The `s`-slice of the stationary stream function is the stream function itself. -/
theorem slice_phiOf3 (Φ : ℝ → ℝ → ℝ) (s : ℝ) : Work.Stability.slice (phiOf3 Φ) s = Φ := rfl

/-- The full profile of the delivered data as a family is the profile `F = F_* + P.g`. -/
theorem Ftot_gOf3 (P : Work.ConstructionInstance.ProfileData α) (s : ℝ) :
    Work.Stability.Ftot (Work.ConstructionInstance.profExp α) (gOf3 P) s = profOf P := by
  funext z θ
  simp only [Work.Stability.Ftot, gOf3, profOf]

/-- **`gDynRHS` of the delivered data is stationary**: with the stationary perturbation `gOf3 P` and
the state `modStateOf κ` (both `s`-independent), the right-hand side of the `g`-equation does not
depend on the self-similar time. -/
theorem gDynRHS_stat (P : Work.ConstructionInstance.ProfileData α) (κ : ℝ)
    (Φ : ℝ → ℝ → ℝ) (z θ s : ℝ) :
    Work.Stability.gDynRHS (Work.ConstructionInstance.profExp α) (modStateOf κ) (gOf3 P)
        (phiOf3 Φ) z θ s
      = Work.Stability.gDynRHS (Work.ConstructionInstance.profExp α) (modStateOf κ) (gOf3 P)
        (phiOf3 Φ) z θ 0 := by
  simp only [Work.Stability.gDynRHS, Ftot_gOf3, modStateOf_kappa, modStateOf_b,
    slice_gOf3, slice_phiOf3]

/-- `GEquationStat` is the vanishing of the `g`-equation residual up to `Far`. -/
theorem gEquationStat_iff (P : Work.ConstructionInstance.ProfileData α) (κ : ℝ)
    (Φ : ℝ → ℝ → ℝ) (Far : ℝ → ℝ → ℝ) :
    GEquationStat P κ Φ Far
      ↔ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → gEqResidual P κ Φ z θ = Far z θ := by
  rw [GEquationStat, Work.Stability.GEquationFar]
  constructor
  · intro h z θ hzθ
    have h1 := h z θ 0 hzθ
    rw [modStateOf_kappa, deriv_gOf3, mul_zero, zero_add, slice_gOf3, farOf3_apply] at h1
    simp only [gEqResidual]
    linarith [h1]
  · intro h z θ s hzθ
    have h1 := h z θ hzθ
    simp only [gEqResidual] at h1
    rw [modStateOf_kappa, deriv_gOf3, mul_zero, zero_add, slice_gOf3,
      gDynRHS_stat P κ Φ z θ s, farOf3_apply]
    linarith [h1]

/-! ## The G-route's honest residual and its identification -/

/-- **The field-level image of a profile-level far-field term**: the `ℝ³`-valued field obtained by
transforming `Far` through the ansatz, including the cut-off and the amplitude factor.  This is the
*only* way a profile-level statement can be read as a deficit of the `ℝ³` vorticity equation, and it
is where the non-locality of the Biot–Savart velocity is hidden. -/
def fieldImage (P : Work.ConstructionInstance.ProfileData α) (Far : ℝ → ℝ → ℝ) : R3 → ℝ → R3 :=
  fun x t => (P.lam t)⁻¹ •
    (Work.Stability.chi (Work.Cyl.rho x / P.L) •
      (Far (Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / P.lam t) (Work.Cyl.theta x) •
        Work.Cyl.eTheta x))

@[simp] theorem fieldImage_apply (P : Work.ConstructionInstance.ProfileData α)
    (Far : ℝ → ℝ → ℝ) (x : R3) (t : ℝ) :
    fieldImage P Far x t = (P.lam t)⁻¹ •
      (Work.Stability.chi (Work.Cyl.rho x / P.L) •
        (Far (Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / P.lam t)
          (Work.Cyl.theta x) • Work.Cyl.eTheta x)) := rfl

/-- The image of the zero profile is zero. -/
theorem fieldImage_zero (P : Work.ConstructionInstance.ProfileData α) :
    fieldImage P (fun _ _ => 0) = fun _ _ => 0 := by
  funext x t
  simp [fieldImage_apply]

/-- **The G-route's honest residual**: the constructed field solves the `ℝ³` vorticity equation *up
to* the explicit deficit `fieldImage P Far`.  `HonestR1 P 0` is exactly the delivered residual
`VortEq α P` (`Work.CoreResiduals.vortEq_iff_noDeficit`); the informative content is the case
`Far ≠ 0` with `Far` the `g`-equation's deficit. -/
def HonestR1 (P : Work.ConstructionInstance.ProfileData α) (Far : ℝ → ℝ → ℝ) : Prop :=
  Work.CoreResiduals.VortEqWithDeficit P (fieldImage P Far)

/-- **The mechanical rewrite**: the honest residual with zero deficit *is* the delivered residual. -/
theorem honestR1_zero_iff (P : Work.ConstructionInstance.ProfileData α) :
    HonestR1 P (fun _ _ => 0) ↔ Work.CoreResiduals.VortEq α P := by
  rw [HonestR1, fieldImage_zero, Work.CoreResiduals.vortEq_iff_noDeficit]

/-- **The deficit cancellation, abstractly**: if the honest residual holds and the deficit vanishes
identically, then the delivered residual `VortEq α P` holds.  This is the step that turns the
G-route's *deficit* identification into the Euler equation itself. -/
theorem vortEq_of_honestR1_of_deficit_eq_zero (P : Work.ConstructionInstance.ProfileData α)
    {Far : ℝ → ℝ → ℝ} (h : HonestR1 P Far) (h0 : ∀ z θ : ℝ, Far z θ = 0) :
    Work.CoreResiduals.VortEq α P := by
  rw [← honestR1_zero_iff P]
  intro x t
  have h1 := h x t
  simp only [fieldImage_apply, h0, zero_smul, smul_zero] at h1 ⊢
  exact h1

/-- **The identification residual of the G-route**: the field-level deficit of the constructed field
is the image of the profile-level far-field term of the `g`-equation.  This is the *one* analytic
statement the honest route needs beyond the `g`-equation: it is the `gDynRHS` identification of the
field-level deficit, i.e. the (non-local) statement that the leftover of the cut field's vorticity
equation is exactly the modulation's deficit — the elliptic-identification side of R1
(`Work.CoreResiduals.NOTES.md` §5(iv)). -/
def DeficitIsGResidual (P : Work.ConstructionInstance.ProfileData α) (Far : ℝ → ℝ → ℝ) : Prop :=
  ∀ x t, Work.CoreResiduals.r1Deficit P x t = fieldImage P Far x t

/-- **The `g`-route theorem**: the deficit identification turns the (unconditional) deficit form of
R1 into the *profile-level* statement.  The deficit form itself carries no information
(`Work.CoreResiduals.vortEqWithDeficit_canonical`); what the identification buys is that the deficit
is the profile-level `g`-equation's far-field term. -/
theorem honestR1_of_identification (P : Work.ConstructionInstance.ProfileData α)
    {Far : ℝ → ℝ → ℝ} (hId : DeficitIsGResidual P Far) : HonestR1 P Far := by
  intro x t
  rw [← hId x t]
  exact Work.CoreResiduals.vortEqWithDeficit_canonical P x t

/-! ## The derivation bundle with the `L₁₂`-splitting restricted to `z ≥ 0`

**Finding (interface).**  The delivered `Work.Stability.GDerivData` quantifies its `hL` field
(`L₁₂(F_* + g) = L₁₂(F_*) + L₁₂(g)`) over **all** `z : ℝ`.  Its only consumer
(`Work.Stability.DynGEquation`, and through it the whole `St2` derivation) uses it on the open
quadrant.  Over all `z` it is **not** derivable from `ProfileData`: for `z < -1` the density
`L12dens (F_*)` has a non-integrable pole at `s = -1`, so `L12 (F_*) z` and `L12 (F_* + g) z` are
both Lean-junk `0` (`MeasureTheory.integral_undef`) while `L12 g z` is generically nonzero.  The
bundle below is the *correct* interface: the same seven fields, with `hL` restricted to `z ≥ 0`.
`GDerivData → GDerivDataQd` and `GDerivDataQd` is derivable from `ProfileData`
(`gDerivDataQd_phi_zero`). -/
structure GDerivDataQd (α : ℝ) (g φ : Work.Stability.F3) : Prop where
  /-- the `Φ = Φ̃ + Θ` decomposition, `z`-part -/
  h2 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pz (Work.Stability.slice φ s) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Stability.Ftot α g s)
            (Work.Stability.slice φ s)) z θ
          + Work.Spaces.pz (Work.Construction.Theta α (Work.Stability.Ftot α g s)) z θ
  /-- the `Φ = Φ̃ + Θ` decomposition, `θ`-part -/
  h3 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Work.Stability.slice φ s) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Stability.Ftot α g s)
            (Work.Stability.slice φ s)) z θ
          + Work.Spaces.pth (Work.Construction.Theta α (Work.Stability.Ftot α g s)) z θ
  /-- the derivative evaluation of `Θ`, `z`-part -/
  h5 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      z * Work.Spaces.pz (Work.Construction.Theta α (Work.Stability.Ftot α g s)) z θ
        = -(1 / (4 * α)) * Work.Construction.s2 θ
            * Work.Construction.FK (Work.Stability.Ftot α g s) z
  /-- the derivative evaluation of `Θ`, `θ`-part -/
  h6 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Work.Construction.Theta α (Work.Stability.Ftot α g s)) z θ
        = (1 / (2 * α)) * Real.cos (2 * θ)
            * Work.Construction.L12 (Work.Stability.Ftot α g s) z
  /-- the `D_z`-splitting over `F = F_* + g` -/
  hDz : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (fun z θ => Work.Stability.Ftot α g s z θ) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          + Work.Spaces.Dz (Work.Stability.slice g s) z θ
  /-- the `∂_θ`-splitting over `F = F_* + g` -/
  hpth : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (fun z θ => Work.Stability.Ftot α g s z θ) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ
          + Work.Spaces.pth (Work.Stability.slice g s) z θ
  /-- the `L₁₂`-splitting over `F = F_* + g`, **on `z ≥ 0`** -/
  hL : ∀ z s, 0 ≤ z → Work.Construction.L12 (Work.Stability.Ftot α g s) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z
        + Work.Construction.L12 (Work.Stability.slice g s) z

/-- The delivered bundle implies the restricted one (the `hL` field is weakened). -/
theorem GDerivDataQd.of_gDerivData {α : ℝ} {g φ : Work.Stability.F3}
    (h : Work.Stability.GDerivData α g φ) : GDerivDataQd α g φ :=
  { h2 := h.h2, h3 := h.h3, h5 := h.h5, h6 := h.h6, hDz := h.hDz, hpth := h.hpth,
    hL := fun z s _ => h.hL z s }

/-! ## The modulated profile data (deliverable 1) -/

/-- **The modulated profile data of the G-route**: a `ProfileData` whose perturbation `g` is
*nonzero* and solves the `St2`/`St3` `g`-equation with the far-field deficit `Far`, at the effective
rate `2κ`, with the stream function `Φ` and the derivation bundle `Work.Stability.GDerivData` that
the construction supplies.  This is "the Construction area's reference profile `F_*` + the Stability
bootstrap's conclusion", i.e. the honest data at which residual R1 is expected to hold — unlike the
delivered inhabitant (`g = 0`), for which R1 provably fails. -/
structure ModulatedData (α : NNReal) where
  /-- the profile/modulation data -/
  P : Work.ConstructionInstance.ProfileData α
  /-- the perturbation is *visible*: it is nonzero at some point of the **open quadrant**, i.e. it
  really perturbs the physical profile (the delivered inhabitant has `g = 0`) -/
  hgnz : ∃ z θ : ℝ, 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 ∧ P.g z θ ≠ 0
  /-- the modulation rate `κ = -λ̄'` of the paper's dilated time -/
  κ : ℝ
  /-- the rate of the modulation on the pre-window -/
  hrate : EffRate P κ
  /-- the stream function of the ansatz -/
  Φ : ℝ → ℝ → ℝ
  /-- the far-field deficit of the `g`-equation -/
  Far : ℝ → ℝ → ℝ
  /-- the `g`-equation with the deficit -/
  hFar : GEquationStat P κ Φ Far
  /-- the derivation bundle of the `St2` derivation, in the form that is *derivable* from
  `ProfileData` (`GDerivDataQd`; the delivered `Work.Stability.GDerivData` quantifies its `L₁₂`
  splitting over all `z`, which fails for `z < -1` — see its docstring) -/
  hD : GDerivDataQd (Work.ConstructionInstance.profExp α) (gOf3 P) (phiOf3 Φ)

/-- The perturbation of a `ModulatedData` is *not* the zero perturbation: this is what makes the
data "modulated" in the sense of the G-route. -/
theorem ModulatedData.g_ne_zero (D : ModulatedData α) : D.P.g ≠ 0 := by
  obtain ⟨z, θ, _, _, _, h⟩ := D.hgnz
  intro h0
  exact h (congrFun (congrFun h0 z) θ)

/-- The `g`-equation residual of a `ModulatedData` is its far-field term. -/
theorem ModulatedData.gEqResidual_eq_far (D : ModulatedData α) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      gEqResidual D.P D.κ D.Φ z θ = D.Far z θ :=
  (gEquationStat_iff D.P D.κ D.Φ D.Far).mp D.hFar


/-! ## The explicit cut-off deficit -/

/-- **The derivative of the cut-off factor in the radial variable**: `χ'(ρ(r,z)/L)/L`.  The
cut-off `χ(ρ/L)` is a function of `ρ` alone, so its `(r,z)`-gradient is `chiRad · (r/ρ, z/ρ)`. -/
def chiRad (P : Work.ConstructionInstance.ProfileData α) (r z : ℝ) : ℝ :=
  deriv Work.Stability.chi (Work.Cyl.rhoP r z / P.L) / P.L

/-- The meridian profile of the **constructed (cut)** field: `W_cut = χ(ρP(r,z)/L)·W` where `W` is
the meridian profile of the *uncut* field (`ssVortOf` for a `ProfileData`). -/
def cutProfile (P : Work.ConstructionInstance.ProfileData α) (W : ℝ → ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ → ℝ :=
  fun r z t => Work.Stability.chi (Work.Cyl.rhoP r z / P.L) * W r z t

theorem cutProfile_apply (P : Work.ConstructionInstance.ProfileData α) (W : ℝ → ℝ → ℝ → ℝ)
    (r z t : ℝ) :
    cutProfile P W r z t = Work.Stability.chi (Work.Cyl.rhoP r z / P.L) * W r z t := rfl

/-- **The explicit cut-off deficit** of the meridian residual: the term picked up by the radial
cut-off `χ(ρ/L)` in the meridian residual of the cut field,

  `(χ'(ρ/L)/L)·( (∂_zψ)·(r/ρ) - (ψ/r + ∂_rψ)·(z/ρ) )·W`.

It is the *only* local obstruction created by the cut-off (see
`Work.R1G.meridianResid_cut`), and it is the deficit that the honest modulation `g ≠ 0` of the
G-route has to cancel. -/
def cutDeficit (P : Work.ConstructionInstance.ProfileData α) (ψ W : ℝ → ℝ → ℝ → ℝ)
    (r z t : ℝ) : ℝ :=
  chiRad P r z *
    (Work.Cyl.pdZ (fun r z => ψ r z t) r z * (r / Work.Cyl.rhoP r z)
      - (ψ r z t / r + Work.Cyl.pdR (fun r z => ψ r z t) r z) * (z / Work.Cyl.rhoP r z))
    * W r z t

theorem cutDeficit_apply (P : Work.ConstructionInstance.ProfileData α)
    (ψ W : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) :
    cutDeficit P ψ W r z t
      = chiRad P r z *
          (Work.Cyl.pdZ (fun r z => ψ r z t) r z * (r / Work.Cyl.rhoP r z)
            - (ψ r z t / r + Work.Cyl.pdR (fun r z => ψ r z t) r z)
                * (z / Work.Cyl.rhoP r z))
          * W r z t := rfl


end Work.R1G
