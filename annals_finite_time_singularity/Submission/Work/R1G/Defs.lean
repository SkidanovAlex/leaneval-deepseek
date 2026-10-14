import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.CoreResiduals.R1Status
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.ModEqn

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



/-! ## The full profile `F = F_* + g` -/



/-- **The perturbation as a family** (`Work.Stability.F3`): the delivered interface's perturbation
`P.g` is *stationary* (it does not depend on the self-similar time `s`).  This is the bridge to the
`St2`/`St3` vocabulary, where the modulation is a family `(z,θ,s) ↦ g(z,θ,s)`. -/
def gOf3 (P : Work.ConstructionInstance.ProfileData α) : Work.Stability.F3 :=
  fun z θ _ => P.g z θ





/-! ## The uncut field and the cut-off decomposition -/





/-! ## The meridian point and the meridian slice -/

/-- **The meridian point** `(r, 0, z) ∈ ℝ³`: the half-plane `x₁ = 0` on which the axisymmetric
fields are represented by their `(r, z)`-profiles.  For `r > 0` this is off the axis, so the
cylindrical frame is regular there. -/
def mkPt (r z : ℝ) : R3 := !₂[r, 0, z]

@[simp] theorem mkPt_apply_zero (r z : ℝ) : mkPt r z 0 = r := rfl
@[simp] theorem mkPt_apply_one (r z : ℝ) : mkPt r z 1 = 0 := rfl
@[simp] theorem mkPt_apply_two (r z : ℝ) : mkPt r z 2 = z := rfl




/-- The `ℝ³` radial coordinate is the meridian `rhoP` of `(radial, axial)`. -/
theorem rho_eq_rhoP (x : R3) :
    Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
  rw [Work.Cyl.rho, Work.Cyl.rhoP]
  congr 1
  rw [Work.Cyl.radial_sq]

/-- The `ℝ³` polar angle is the meridian `thetaP` of `(radial, axial)`. -/
theorem theta_eq_thetaP (x : R3) :
    Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl



/-! ## The modulation rate, and the profile equation at the effective rate -/

/-- **The modulation rate**: `κ` with `λ̄'(t) = -κ` on the pre-window.  This is the design's
`κ = -λ̄'` (`Work.Stability.Defs`), the rate in the paper's *dilated* time; the rate entering the
*physical* profile equation of residual R1 is `2κ` (`Model.model_rate_physical`). -/
def EffRate (P : Work.ConstructionInstance.ProfileData α) (κ : ℝ) : Prop :=
  ∀ t ∈ Work.ConstructionInstance.preWindow P.T, HasDerivAt P.lam (-κ) t


/-- **The profile-level residual** of the G-route: the left-hand side of the profile equation at the
effective rate `2κ`, i.e. `2κ·(F + D_zF) + UVR p F Φ` with `F = F_* + P.g`; its vanishing on the
open quadrant is `ProfileEq`. -/
def profileResidGen (p κ : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * κ * (F z θ + Work.Spaces.Dz F z θ)
    + Work.Construction.UVR p F Φ z θ





/-! ## The meridian pair of a `ProfileData` -/






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



end Work.R1G
