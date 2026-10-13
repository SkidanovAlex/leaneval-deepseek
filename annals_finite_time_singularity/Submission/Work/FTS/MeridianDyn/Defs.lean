/-
# `Work.FTS.MeridianDyn.Defs` — the dynamic meridian bridge: vocabulary

This directory (`Submission/Work/FTS/MeridianDyn/`, namespace `Work.FTS.MeridianDyn`) is the
**dynamic meridian bridge** of the Elgindi finite-time-singularity project: it carries the passage
from the *fake-time* (dynamically rescaled) profile equation of the modulation analysis to the
**meridian scalar equation** in the physical variables `(r, z, t)`,

  `∂ₜW + (∂_zψ)·∂_rW + ( -(ψ/r) - ∂_rψ )·∂_zW = ((∂_zψ)/r)·W`   (`r > 0`),

whose residual is `Work.CoreResiduals.meridianResid`.  It generalises the *constant-rate* chain-rule
reduction `Work.CoreResiduals.meridianEq_of_dynEqConst` / `meridianResid_algebra` to the
*dynamically rescaled* ansatz of node N5/N7:

  `W(r,z,t) = a(t)·F(ρ(r,z)^p / b(t), Θ(r,z), σ(t))`,   `ψ(r,z,t) = ρ(r,z)²·a(t)·Φ(…, σ(t))`,

where `ρ = √(r²+z²)`, `Θ = arctan(z/r)`, `a` is the amplitude (`a = A_v⁻¹`), `b` the space scale
(`b = B`), and `σ` the fake-time clock (in the reconstruction, `σ = clockInv C`).

## The two equations

* the **meridian equation** (`Work.CoreResiduals.MeridianEq`, recovered here on a time window as
  `MeridianEqOn`);
* the **dynamic profile equation** `DynEqF α μ F Φ`, i.e. the paper's modulation equation in the
  `(z,θ,τ)` variables at the *τ-dependent* rate `μ` (written `(E)` in the design
  `Submission/Work/FTS/FTS_PHYS_BRIDGE.md` §3, item 9):

  `∂_τ F + (1+μ(τ))·F + (1-μ(τ))·D_z F + UVR α F Φ = 0`   on the open quadrant, `τ > 0`.

The passage from the fake-time `g`-equation `Galerkin.IsDynEqOn` to `(E)` is `dynEqF_of_isDynEqOn`
(module `DynEqF`); the passage from `(E)` to the meridian equation is `meridianEq_of_dynEq`
(module `Main`), through the pointwise chain-rule identity `meridianResid_dyn` (module `ResidDyn`).

## Conventions (pinned here, once)

* `p` is the **profile exponent** `ρ^p` of the self-similar ansatz; in the reconstruction
  `p = Work.FTS.Regularity.pExp α = 3α` (`Work.ConstructionInstance.profExp`).  The same symbol is
  the exponent parameter of `Work.Construction.UVR` (the paper's `α`-slot), so all statements below
  take a *single* exponent, always called `α` in the `UVR`/`MainLHS`/`LΓ^T` slot and `p` in the
  `ρ^p` slot; they coincide in every application.
* the factor `2` of the clock: the physical amplitude is `A_v = A` with `A' = -(1+μ)A`, and the
  clock satisfies `σ' = 1/C.A`, `C.A = 2·A_v` (correction 1 of the design §0/§3).  With these two
  normalisations the meridian identity reads `resid = a·σ'·(E)` (module `ResidDyn`).
* the *sign* convention of correction 1: the physical vorticity is `ω = −physOmega`, i.e. the
  meridian profile is `−merProfile`; every statement of this directory is stated for the
  `physOmega` sign and transported by linearity (`MeridianEqOn.neg_left`).
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.Physical.Meridian
import Submission.Work.FTS.Physical.Clock.clockInv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology

namespace Work.FTS.MeridianDyn

set_option autoImplicit false

/-! ## Families of fake-time profiles -/

/-- A family `(z,θ,τ) ↦ g z θ τ` of fake-time profiles (same as `Work.FTS.Galerkin.Fam`). -/
abbrev Fam := Work.FTS.Galerkin.Fam

/-- The `τ`-slice of a family. -/
def slice (F : Fam) (τ : ℝ) : ℝ → ℝ → ℝ := fun z θ => F z θ τ

@[simp] theorem slice_apply (F : Fam) (τ z θ : ℝ) : slice F τ z θ = F z θ τ := rfl

/-- The family of *full* profiles `F = F_* + g(τ)`: `Work.Construction.Ftau` read as a family of
`(Z,Θ,σ)`.  This is the profile whose `(E)` is the content of `dynEqF_of_isDynEqOn`. -/
def profFam (α : ℝ) (g : Fam) : Fam := fun Z Θ σ => Work.Construction.Ftau α g σ Z Θ

@[simp] theorem profFam_apply (α : ℝ) (g : Fam) (Z Θ σ : ℝ) :
    profFam α g Z Θ σ = Work.Construction.Ftau α g σ Z Θ := rfl

theorem profFam_eq (α : ℝ) (g : Fam) (Z Θ σ : ℝ) :
    profFam α g Z Θ σ = Work.Construction.Fstar α Z Θ + g Z Θ σ := rfl

/-- The full profile with the paper's **odd extension in `θ`**, which is the form the physical
meridian profile `Work.FTS.Physical.merProfile` uses (`Work.ConstructionInstance.profile`):
`profFamOdd α g Z Θ σ = profile α (g(·,·,σ)) Z Θ`, i.e. `F_* + g` for `θ ≥ 0` and its odd
continuation for `θ < 0`. -/
def profFamOdd (α : ℝ) (g : Fam) : Fam :=
  fun Z Θ σ => Work.ConstructionInstance.profile α (Work.FTS.Regularity.gSlice g σ) Z Θ

@[simp] theorem profFamOdd_apply (α : ℝ) (g : Fam) (Z Θ σ : ℝ) :
    profFamOdd α g Z Θ σ
      = Work.ConstructionInstance.profile α (Work.FTS.Regularity.gSlice g σ) Z Θ := rfl

theorem profFamOdd_of_nonneg {α : ℝ} {g : Fam} {Z Θ σ : ℝ} (h : 0 ≤ Θ) :
    profFamOdd α g Z Θ σ = profFam α g Z Θ σ := by
  rw [profFamOdd_apply, profFam_apply, Work.ConstructionInstance.profile_of_nonneg h]
  rfl

/-! ## The dynamical self-similar ansatz -/

/-- **The dynamical self-similar ansatz for the vorticity**:
`W(r,z,t) = a(t)·F(ρ(r,z)^p/b(t), Θ(r,z), σ(t))`, `ρ = √(r²+z²) = Work.Cyl.rhoP`,
`Θ = arctan(z/r) = Work.Cyl.thetaP`.

A `a` is the amplitude (`A_v⁻¹` in the reconstruction), `b` the space scale, `σ` the fake-time
clock and `F` the profile family.  This generalises `Work.CoreResiduals.ssVort` (the constant-rate
case `a = λ⁻¹`, `b = λ`, `σ = id`). -/
def dynVort (p : ℝ) (a b σ : ℝ → ℝ) (F : Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun r z t => a t * F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)

/-- **The dynamical self-similar ansatz for the stream function**:
`ψ(r,z,t) = ρ(r,z)²·a(t)·Φ(ρ(r,z)^p/b(t), Θ(r,z), σ(t))`.  This is the physical stream function of
the swirl field (`Work.Cyl.psiField`'s `ψ`), generalising `Work.CoreResiduals.ssPsi`. -/
def dynPsi (p : ℝ) (a b σ : ℝ → ℝ) (Φ : Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun r z t => Work.Cyl.rhoP r z ^ 2 * a t
    * Φ (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)

@[simp] theorem dynVort_apply (p : ℝ) (a b σ : ℝ → ℝ) (F : Fam) (r z t : ℝ) :
    dynVort p a b σ F r z t = a t * F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
      (σ t) := rfl

@[simp] theorem dynPsi_apply (p : ℝ) (a b σ : ℝ → ℝ) (Φ : Fam) (r z t : ℝ) :
    dynPsi p a b σ Φ r z t = Work.Cyl.rhoP r z ^ 2 * a t
      * Φ (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t) := rfl

/-! ## The dynamic profile equation `(E)` -/

/-- The left-hand side of the **dynamic profile equation** `(E)` at a point, with the fake-time
derivative `Fτ` supplied as a parameter:

  `Fτ + (1+μ)·F(Z,Θ) + (1-μ)·D_z F(Z,Θ) + UVR α F Φ (Z,Θ)`. -/
def dynEqLHS (α : ℝ) (μ : ℝ) (F Φ : ℝ → ℝ → ℝ) (Z Θ Fτ : ℝ) : ℝ :=
  Fτ + (1 + μ) * F Z Θ + (1 - μ) * Work.Spaces.Dz F Z Θ + Work.Construction.UVR α F Φ Z Θ

@[simp] theorem dynEqLHS_apply (α : ℝ) (μ : ℝ) (F Φ : ℝ → ℝ → ℝ) (Z Θ Fτ : ℝ) :
    dynEqLHS α μ F Φ Z Θ Fτ
      = Fτ + (1 + μ) * F Z Θ + (1 - μ) * Work.Spaces.Dz F Z Θ
        + Work.Construction.UVR α F Φ Z Θ := rfl

/-- **The dynamic profile equation `(E)`** (design `FTS_PHYS_BRIDGE.md` §3, item 9): the paper's
modulation equation for the *full* profile `F = F_* + g` in the fake-time variables, at the
`τ`-dependent modulation `1+μ` and the paper's second rate `b = (1-μ)/(1+μ)`:

  `∂_τ F + (1+μ(τ))·F + (1-μ(τ))·D_z F + UVR α F Φ = 0`   on the open quadrant, for `τ > 0`.

It is the equation the pair `(F, Φ)` satisfies for the dynamically rescaled solution; the
fake-time `g`-equation `Work.FTS.Galerkin.IsDynEqOn` implies it at `μ = Work.FTS.Galerkin.muDyn`
(`dynEqF_of_isDynEqOn`). -/
def DynEqF (α : ℝ) (μ : ℝ → ℝ) (F Φ : Fam) : Prop :=
  ∀ z θ τ : ℝ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
    deriv (fun s => F z θ s) τ + (1 + μ τ) * F z θ τ
      + (1 - μ τ) * Work.Spaces.Dz (slice F τ) z θ
      + Work.Construction.UVR α (slice F τ) (slice Φ τ) z θ = 0

theorem DynEqF.eq {α : ℝ} {μ : ℝ → ℝ} {F Φ : Fam} (h : DynEqF α μ F Φ) :
    ∀ z θ τ : ℝ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      deriv (fun s => F z θ s) τ + (1 + μ τ) * F z θ τ
        + (1 - μ τ) * Work.Spaces.Dz (slice F τ) z θ
        + Work.Construction.UVR α (slice F τ) (slice Φ τ) z θ = 0 := h

/-- The pointwise form of `DynEqF` at `(Z,Θ)` with the family derivative `Fτ` given explicitly;
this is the shape in which the meridian chain rule consumes it. -/
theorem DynEqF.pointwise {α : ℝ} {μ : ℝ → ℝ} {F Φ : Fam} (h : DynEqF α μ F Φ)
    {Z Θ τ : ℝ} (hZ : (Z, Θ) ∈ Work.Construction.Qd) (hτ : 0 < τ) :
    dynEqLHS α (μ τ) (slice F τ) (slice Φ τ) Z Θ (deriv (fun s => F Z Θ s) τ) = 0 := by
  have h0 := h Z Θ τ hZ hτ
  rw [dynEqLHS_apply]
  simpa only [slice_apply, Work.Spaces.Dz] using h0

/-! ## The meridian equation on a time window -/

/-- **The meridian scalar equation on the time window `(0,T)`**, off the axis `r > 0` and off the
equatorial plane `z ≠ 0` (the complement of the union of the two is the null set on which the
physical reconstruction is undefined).  This is the predicate the physical reconstruction consumes
(both the audit's `hmer` and the design's `MeridianEqOn`): the pointwise vanishing of
`Work.CoreResiduals.meridianResid` on `(0,∞) × {z ≠ 0} × (0,T)`. -/
def MeridianEqOn (W ψ : ℝ → ℝ → ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ r z t : ℝ, 0 < r → z ≠ 0 → t ∈ Set.Ioo 0 T →
    Work.CoreResiduals.meridianResid W ψ r z t = 0

/-- `MeridianEqOn` only depends on the window through its time interval. -/
theorem MeridianEqOn.mono {W ψ : ℝ → ℝ → ℝ → ℝ} {T T' : ℝ} (h : MeridianEqOn W ψ T)
    (hT'T : T' ≤ T) : MeridianEqOn W ψ T' :=
  fun r z t hr hz ht => h r z t hr hz ⟨ht.1, lt_of_lt_of_le ht.2 hT'T⟩

/-- The residual is linear in the vorticity profile: negating `W` negates the meridian residual.
This is the transport of the **sign convention of correction 1** (`ω = −physOmega`). -/
theorem meridianResid_neg_left (W ψ : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) :
    Work.CoreResiduals.meridianResid (fun r z t => -(W r z t)) ψ r z t
      = -Work.CoreResiduals.meridianResid W ψ r z t := by
  have hneg : ∀ (f : ℝ → ℝ) (x : ℝ), deriv (fun y => -f y) x = -deriv f x :=
    fun f x => deriv.neg
  unfold Work.CoreResiduals.meridianResid
  simp only [Work.Cyl.pdR, Work.Cyl.pdZ, hneg]
  ring

/-- **The meridian equation is invariant under negating the vorticity profile** — the sign
convention of correction 1: with `ω = −physOmega`, the meridian profile is `−merProfile`, and
`MeridianEqOn` transfers. -/
theorem MeridianEqOn.neg_left {W ψ : ℝ → ℝ → ℝ → ℝ} {T : ℝ} (h : MeridianEqOn W ψ T) :
    MeridianEqOn (fun r z t => -(W r z t)) ψ T :=
  fun r z t hr hz ht => by
    rw [meridianResid_neg_left, h r z t hr hz ht, neg_zero]

/-! ## The reconstruction's meridian pair -/

/-- **The physical stream function of the reconstruction**,
`ψ(r,z,t) = ρ(r,z)²·(A(σ(t)))⁻¹·Φ(ρ(r,z)^p/B(σ(t)), Θ(r,z), σ(t))` with `σ = clockInv C`.

This is the time-dependent companion of `Work.FTS.Physical.Ident.merPsi` (which is the static
`t`-free form) and the stream function of the ansatz velocity
`Work.Cyl.psiField (fun r z => merPsi p A B Φ C r z t)`. -/
def merPsi (p : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Work.FTS.Physical.PhysClock) :
    ℝ → ℝ → ℝ → ℝ :=
  dynPsi p (fun t => (A (Work.FTS.Physical.clockInv C t))⁻¹)
    (fun t => B (Work.FTS.Physical.clockInv C t)) (Work.FTS.Physical.clockInv C) Φ

/-- **The physical vorticity profile of the reconstruction** (the `e_θ`-coefficient of
`physOmega`), realised as an instance of the general ansatz `dynVort`.  It is *definitionally* the
`Work.FTS.Physical.merProfile` of the frozen physical layer. -/
def merProfileDyn (α : ℝ) (A B : ℝ → ℝ) (g : Fam) (C : Work.FTS.Physical.PhysClock) :
    ℝ → ℝ → ℝ → ℝ :=
  dynVort (Work.FTS.Regularity.pExp α) (fun t => (A (Work.FTS.Physical.clockInv C t))⁻¹)
    (fun t => B (Work.FTS.Physical.clockInv C t)) (Work.FTS.Physical.clockInv C)
    (profFamOdd (Work.FTS.Regularity.pExp α) g)

/-- **`merProfileDyn` is the frozen `Work.FTS.Physical.merProfile`** (definitional). -/
theorem merProfileDyn_eq (α : ℝ) (A B : ℝ → ℝ) (g : Fam)
    (C : Work.FTS.Physical.PhysClock) :
    merProfileDyn α A B g C = Work.FTS.Physical.merProfile α A B g C := rfl

theorem merProfileDyn_apply (α : ℝ) (A B : ℝ → ℝ) (g : Fam)
    (C : Work.FTS.Physical.PhysClock) (r z t : ℝ) :
    merProfileDyn α A B g C r z t = Work.FTS.Physical.merProfile α A B g C r z t := rfl

/-- `merProfileDyn` is the general ansatz at the profile `profFamOdd`. -/
theorem merProfileDyn_apply' (α : ℝ) (A B : ℝ → ℝ) (g : Fam)
    (C : Work.FTS.Physical.PhysClock) (r z t : ℝ) :
    merProfileDyn α A B g C r z t
      = (A (Work.FTS.Physical.clockInv C t))⁻¹
        * profFamOdd (Work.FTS.Regularity.pExp α) g
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
              / B (Work.FTS.Physical.clockInv C t))
            (Work.Cyl.thetaP r z) (Work.FTS.Physical.clockInv C t) := rfl

/-- On the positive-angle branch the profile of `merProfileDyn` is the full profile `F_* + g`. -/
theorem merProfileDyn_of_nonneg (α : ℝ) (A B : ℝ → ℝ) (g : Fam)
    (C : Work.FTS.Physical.PhysClock) {r z t : ℝ} (hθ : 0 ≤ Work.Cyl.thetaP r z) :
    merProfileDyn α A B g C r z t
      = (A (Work.FTS.Physical.clockInv C t))⁻¹
        * profFam (Work.FTS.Regularity.pExp α) g
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
              / B (Work.FTS.Physical.clockInv C t))
            (Work.Cyl.thetaP r z) (Work.FTS.Physical.clockInv C t) := by
  rw [merProfileDyn_apply', profFamOdd_of_nonneg hθ]

/-! ## The vorticity equation, sliced in time -/

/-- **The `ℝ³` vorticity equation for the meridian pair `(W, Ψ)` at time `t`**: the pointwise
form of `Work.LWP.VorticityEquation` for the swirl vorticity `W(radial x, axial x, t) • e_θ(x)`
and the stream-function velocity `x ↦ psiField (Ψ · t) x`.  Slicing in `t` is what allows the
equation to be asserted on a time window `(0,T)` only. -/
def VorticityEquationAt (W Ψ : ℝ → ℝ → ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ x : Work.Cyl.R3,
    timeDeriv
        (fun x s => W (Work.Cyl.radial x) (Work.Cyl.axial x) s • Work.Cyl.eTheta x) x t
      + directionalDeriv
          (fun x s => W (Work.Cyl.radial x) (Work.Cyl.axial x) s • Work.Cyl.eTheta x)
          (fun x s => Work.Cyl.psiField (fun r z => Ψ r z s) x) x t
      = directionalDeriv
          (fun x s => Work.Cyl.psiField (fun r z => Ψ r z s) x)
          (fun x s => W (Work.Cyl.radial x) (Work.Cyl.axial x) s • Work.Cyl.eTheta x) x t

/-- **The vorticity equation on the time window `(0,T)`**, for the meridian pair `(W, Ψ)`.  This is
the form in which the reconstruction consumes it (it is the `VorticityEquation` clause of
`Work.FTS.Physical.BlowupAt`, restricted to `[0,T)`). -/
def VorticityEquationOn (W Ψ : ℝ → ℝ → ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ t : ℝ, t ∈ Set.Ioo 0 T → VorticityEquationAt W Ψ t

/-- The sliced predicate over all times is exactly `Work.LWP.VorticityEquation`. -/
theorem vorticityEquation_iff_forall_at (W Ψ : ℝ → ℝ → ℝ → ℝ) :
    Work.LWP.VorticityEquation (fun x t => Work.Cyl.psiField (fun r z => Ψ r z t) x)
        (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
      ↔ ∀ t : ℝ, VorticityEquationAt W Ψ t := by
  simp only [Work.LWP.VorticityEquation, VorticityEquationAt]
  exact ⟨fun h t x => h x t, fun h x t => h t x⟩

/-- `VorticityEquationOn` is monotone in the window. -/
theorem VorticityEquationOn.mono {W Ψ : ℝ → ℝ → ℝ → ℝ} {T T' : ℝ}
    (h : VorticityEquationOn W Ψ T) (hT'T : T' ≤ T) : VorticityEquationOn W Ψ T' :=
  fun t ht => h t ⟨ht.1, lt_of_lt_of_le ht.2 hT'T⟩

/-- **The candidate equation bundle** consumed by `dynEqF_of_isDynEqOn`: the *static* derivation
data of the `St2` chain (tex 1343--1369) at the family `(F_* + g(·), Φ(·))`.  This is *not* a
reduction of the target statement: the seven fields are honest identities of the explicit profile
`F_* + g` and its stream function `Φ` (linearity of `D_z`, `∂_θ`, `L₁₂` over the sum `F_* + g`, the
decomposition `Φ = (Φ−Θ) + Θ` and the two derivative evaluations of `Θ`), all of which are
*derivable* from regularity (`profDerivData_of_regPkg`).  Its fields are exactly those of
`Work.R1G.GDerivDataQd` (`hL` restricted to `z ≥ 0`, which is the only region the derivation
uses). -/
structure ProfDerivData (α : ℝ) (Φ g : Fam) : Prop where
  /-- the `Φ = Φ̃ + Θ` decomposition, `z`-part -/
  h2 : ∀ z θ τ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      Work.Spaces.pz (Work.FTS.Galerkin.slice Φ τ) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ)
            (Work.FTS.Galerkin.slice Φ τ)) z θ
          + Work.Spaces.pz (Work.Construction.Theta α (Work.Construction.Ftau α g τ)) z θ
  /-- the `Φ = Φ̃ + Θ` decomposition, `θ`-part -/
  h3 : ∀ z θ τ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      Work.Spaces.pth (Work.FTS.Galerkin.slice Φ τ) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ)
            (Work.FTS.Galerkin.slice Φ τ)) z θ
          + Work.Spaces.pth (Work.Construction.Theta α (Work.Construction.Ftau α g τ)) z θ
  /-- the derivative evaluation of `Θ`, `z`-part -/
  h5 : ∀ z θ τ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      z * Work.Spaces.pz (Work.Construction.Theta α (Work.Construction.Ftau α g τ)) z θ
        = -(1 / (4 * α)) * Work.Construction.s2 θ
            * Work.Construction.FK (Work.Construction.Ftau α g τ) z
  /-- the derivative evaluation of `Θ`, `θ`-part -/
  h6 : ∀ z θ τ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      Work.Spaces.pth (Work.Construction.Theta α (Work.Construction.Ftau α g τ)) z θ
        = (1 / (2 * α)) * Real.cos (2 * θ)
            * Work.Construction.L12 (Work.Construction.Ftau α g τ) z
  /-- the `D_z`-splitting over `F = F_* + g` -/
  hDz : ∀ z θ τ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      Work.Spaces.Dz (Work.Construction.Ftau α g τ) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          + Work.Spaces.Dz (Work.FTS.Galerkin.slice g τ) z θ
  /-- the `∂_θ`-splitting over `F = F_* + g` -/
  hpth : ∀ z θ τ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ
          + Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z θ
  /-- the `L₁₂`-splitting over `F = F_* + g`, on `z ≥ 0` -/
  hL : ∀ z τ, 0 ≤ z → 0 < τ → Work.Construction.L12 (Work.Construction.Ftau α g τ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z
        + Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) z

/-- The `τ`-slice of the family of full profiles `profFam α g` is `Construction.Ftau α g τ`. -/
theorem slice_profFam (α : ℝ) (g : Fam) (τ : ℝ) :
    slice (profFam α g) τ = Work.Construction.Ftau α g τ := rfl

/-- The `τ`-slice of `profFam α g` at `(z,θ)`. -/
@[simp] theorem slice_profFam_apply (α : ℝ) (g : Fam) (τ z θ : ℝ) :
    slice (profFam α g) τ z θ = Work.Construction.Ftau α g τ z θ := rfl

end Work.FTS.MeridianDyn
