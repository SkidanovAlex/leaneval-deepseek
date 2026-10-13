/-
# The STABILITY layer of the Elgindi finite-time-singularity project — **St0: definitions**

This directory (`Submission/Work/Stability/`) is the *stability layer* of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), 1--70,

i.e. the dynamic-modulation bootstrap that turns the *stationary* self-similar solution of
§Modulation (the Construction area, tex 1317--1578) into a solution of the Euler equations
whose vorticity is *compactly supported* (EGM-style localisation).  The design of the layer is
in `NOTES_LEAD_Stability.md` in the workspace root; this file is **St0** of that design and it
pins the conventions everything above it depends on.

## The state and the parametrisation

With physical time `t`, a positive amplitude scale `λ̄` and a positive space scale `μ̄`, the
self-similar ansatz is

  `Ω(R,θ,t) = λ̄(t)^{-1} F(R/μ̄(t), θ)`,   `Ψ(R,θ,t) = λ̄(t)^{-1} Φ(R/μ̄(t), θ)`,
  `R = ρ^α` (`Work.Cyl.Rc α`),  `z = R/μ̄(t)`.

The *self-similar time* is `s := -ln λ̄(t)`; we normalise `λ̄(s) = e^{-s}` (equivalently `s = -ln λ̄`
with `λ̄(0) = 1`).  The two modulation **rates** are

* `κ(s) := -dλ̄/dt` — the *amplitude rate*; it is the coefficient of `F` in the rescaled
  vorticity equation, and it is the quantity called `1+μ` in the stationary problem;
* `b(s)` — the *space-scale rate*, defined by `d ln μ̄/ds = -b`, i.e. `∂_t z = b κ z` at fixed
  `R`; in the stationary problem `b = 1+λ`.

**The `(μ,λ) ↔ (κ,b)` dictionary, pinned once here.**  For the *reference* (stationary)
modulation of the Construction area the two rates are the constants

  `κ* = kappaStar μ := 1 + μ`  and  `b* = bStar μ := 1 + λ = 1 - 2μ/(1+μ) = (1-μ)/(1+μ)`,

so that `κ*·b* = 1 - μ`, which is exactly the paper's choice `μ+λ+μλ = -μ`
(`kappaStar_mul_bStar`).  The dynamical *mismatch rates* are

  `c₁(s) := 2(κ(s) - κ*)`,  `c₂(s) := 2(κ(s)b(s) - κ*b*)`,

so that `κ = κ* + c₁/2` and `κb = κ*b* + c₂/2`; `c₁` plays the role of `2μ` and `c₂` the role
of `2(μ+λ+μλ)`.

*Design note (the "1/2-dilation trap").*  The design writes `κ := -λ̄'/λ̄`; the two conventions
differ by the factor `λ̄ = e^{-s}`.  Only `κ := -λ̄' = λ̄·(-λ̄'/λ̄)` keeps `κ* = 1+μ` *constant*
along the reference solution `λ̄ = 1-(1+μ)t`, and constant reference rates are what every
estimate of the Construction area is calibrated against.  We therefore use `κ = -λ̄'` and
record it here, once, for the whole layer.

## The rescaled equations

With `U, V, ℛ` the operators of (Relations) (tex 1319) and `UVR α F Φ = 2U(Φ)∂_θF + 2αV(Φ)D_zF -
2ℛ(Φ)F` (`Work.Construction.UVR`), the *physical* self-similar vorticity equation is
`SelfSimEuler` below (tex 1319, with the paper's `1/2` time dilation).  Substituting the ansatz
and dividing by `λ̄²` turns it into the **dynamical rescaled equation**

  `κ(s)[∂_s f + f + b(s) D_z f] + UVR α f φ = 0`   (`DynEq`),

which for constant `(κ,b) = (κ*,b*)` and `∂_s f = 0` is exactly the stationary equation
`StatEqF` of the Construction area.

## The `g`-equation

With `F = F_* + g` (`Fstar = α(Γ/c)2z/(1+z)²`, independent of `s`) and `g` carrying all the time
dependence, substituting into `DynEq` and using the paper's chain of identities (tex 1343--1369,
formalised in the Construction area as `MainLHS_explicit`, `UVR_sub`, `LGammaT_eq`) gives the
**dynamical `g`-equation** (`GEquation`, derived in St2, `Submission/Work/Stability/ModEqn.lean`)

  `κ ∂_s g + 𝓛_Γ^T(g) = -(κ-1)F_* - (κb-1)D_zF_* + AK·L₁₂(Transport g)(0) + N₀ + N + N_*`.

The forcing splits (`forcing_split`) into the *mismatch* `-(c₁/2)F_* - (c₂/2)D_zF_*` plus the
*reference* forcing `-μF_* + μD_zF_* = refForcing`, which by `F_* - D_zF_* = 2α·AK` equals
`-2αμ·AK + AK·L₁₂(Transport g)(0)`.

The *far-field* term `Far` of the design is **not** part of this derivation: it is the deficit
incurred by the compactly supported (cut-off) solution, and it enters through the equations
`GEquationFar` / `Work.Stability.GEquationWithFar` as the single *named* hypothesis of the layer
(see `NOTES.md`).

## The orthogonality conditions

* `OrthL12 g := ∀ s, L₁₂(g(·,·,s))(0) = 0` — the condition that makes the projector `𝕡` of
  `𝓛_Γ^T` well behaved (tex 1362-1369, 1567-1568);
* `QuadVanish g` — `g` and `∂_z g` vanish on `{z = 0}`: the second-order vanishing of the
  perturbation (tex 1355-1357), which places `F = F_*+g` in the weighted spaces `ℋ^k`
  (`Work.Spaces.SmoothCompact_HkInf`'s `hz0` hypothesis);

## What this file delivers

The structures and definitions `ModState`, `kappaStar`, `bStar`, `c1`, `c2`, `amp`, `space`,
`scaleZ`, `scaleZx`, `rescaled`, `gPert`, `Ftot`, `slice`, `OrthL12`, `QuadVanish`, `dynLHS`,
`DynEq`, `DynEqHasDeriv`, `SelfSimEuler`, `gDynRHS`, `GEquation`, `GEquationFar`, `refForcing`,
together with their elementary API.  Everything here is a definition or an elementary identity:
this is the interface in which the rest of the layer is stated.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Construction.Main
import Submission.Work.Cyl
import Submission.Work.Coercivity.H4Assembly
import Submission.Work.Spaces.SmoothCompact_HkInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Stability

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Abbreviations -/

/-- A function of the self-similar variables `(z,θ)`. -/
abbrev F2 := ℝ → ℝ → ℝ

/-- A family `(z,θ,s) ↦ ·` of functions of the self-similar variables, parametrised by the
self-similar time `s`. -/
abbrev F3 := ℝ → ℝ → ℝ → ℝ

/-- The `s`-slice of a family: `slice g s = g(·,·,s)`. -/
def slice (g : F3) (s : ℝ) : F2 := fun z θ => g z θ s

theorem slice_apply (g : F3) (s z θ : ℝ) : slice g s z θ = g z θ s := rfl

/-! ## The reference rates and the `(μ,λ) ↔ (κ,b)` dictionary -/

/-- The reference amplitude rate `κ* = 1+μ` (Construction's `1+μ`). -/
def kappaStar (μ : ℝ) : ℝ := 1 + μ

/-- The reference space-scale rate `b* = 1+λ` with the paper's `λ = -2μ/(1+μ)`
(`Work.Construction.lamfun`). -/
def bStar (μ : ℝ) : ℝ := 1 + Work.Construction.lamfun μ

theorem kappaStar_eq (μ : ℝ) : kappaStar μ = 1 + μ := rfl

theorem bStar_eq (μ : ℝ) : bStar μ = 1 - 2 * μ / (1 + μ) := by
  rw [bStar, Work.Construction.lamfun]; ring

/-- `b* = 1+λ` in the paper's `λ`-form. -/
theorem bStar_eq_lamfun (μ : ℝ) : bStar μ = 1 + Work.Construction.lamfun μ := rfl

/-- `λ = b* - 1 = -2μ/(1+μ)`. -/
theorem bStar_sub_one (μ : ℝ) : bStar μ - 1 = Work.Construction.lamfun μ := by
  rw [bStar]; ring

/-- **The dictionary identity `κ*·b* = 1-μ`**, which is exactly the paper's choice
`μ + λ + μλ = -μ` (`hlam`): it is what makes the reference forcing collapse to `-2αμ·AK`
through `F_* - D_zF_* = 2α·AK`. -/
theorem kappaStar_mul_bStar (μ : ℝ) (hμ : 1 + μ ≠ 0) :
    kappaStar μ * bStar μ = 1 - μ := by
  rw [kappaStar_eq, bStar_eq]
  field_simp
  ring

/-! ## The modulation state -/

/-- **The modulation state**: the two *rates* `(κ,b)` of the self-similar rescaling, as
functions of the self-similar time `s`.  `κ` is the amplitude rate (the coefficient of `F` in
the rescaled vorticity equation) and `b` is the space-scale rate.  The amplitude and space
*scales* are recovered from the rates by `amp` and `space` below. -/
structure ModState where
  /-- the amplitude rate `κ(s)`. -/
  kappa : ℝ → ℝ
  /-- the space-scale rate `b(s)`. -/
  b : ℝ → ℝ

namespace ModState

variable (M : ModState)

/-- The **mismatch rate** `c₁(s) = 2(κ(s) - κ*)`: twice the deviation of the amplitude rate
from the reference `κ* = 1+μ`.  It plays the role of `2μ` of the stationary problem. -/
def c1 (μ : ℝ) (M : ModState) (s : ℝ) : ℝ := 2 * (M.kappa s - kappaStar μ)

/-- The **mismatch rate** `c₂(s) = 2(κ(s)b(s) - κ*b*)`: twice the deviation of the product of
the rates from the reference product.  It plays the role of `2(μ+λ+μλ)`. -/
def c2 (μ : ℝ) (M : ModState) (s : ℝ) : ℝ :=
  2 * (M.kappa s * M.b s - kappaStar μ * bStar μ)

theorem c1_apply (μ : ℝ) (s : ℝ) : M.c1 μ s = 2 * (M.kappa s - kappaStar μ) := rfl

theorem c2_apply (μ : ℝ) (s : ℝ) :
    M.c2 μ s = 2 * (M.kappa s * M.b s - kappaStar μ * bStar μ) := rfl

/-- If the state is at the reference amplitude rate at time `s` then `c₁` vanishes. -/
theorem c1_eq_zero_of_eq {μ s : ℝ} (h : M.kappa s = kappaStar μ) : M.c1 μ s = 0 := by
  rw [c1, h]; ring

/-- If the state is at the reference rates at time `s` then `c₂` vanishes. -/
theorem c2_eq_zero_of_eq {μ s : ℝ}
    (h : M.kappa s * M.b s = kappaStar μ * bStar μ) : M.c2 μ s = 0 := by
  rw [c2, h]; ring

/-- The amplitude rate through `c₁`: `κ = κ* + c₁/2`. -/
theorem kappa_eq_kappaStar_add (μ s : ℝ) :
    M.kappa s = kappaStar μ + M.c1 μ s / 2 := by rw [c1]; ring

/-- The product of the rates through `c₂`: `κb = κ*b* + c₂/2`. -/
theorem kappa_mul_b_eq (μ s : ℝ) :
    M.kappa s * M.b s = kappaStar μ * bStar μ + M.c2 μ s / 2 := by rw [c2]; ring

theorem c1_sub (μ s : ℝ) : M.c1 μ s / 2 = M.kappa s - kappaStar μ := by rw [c1]; ring

theorem c2_sub (μ s : ℝ) :
    M.c2 μ s / 2 = M.kappa s * M.b s - kappaStar μ * bStar μ := by rw [c2]; ring

/-- The forcing `-(κ-1)F_* - (κb-1)D_zF_*` of the `g`-equation splits into the **mismatch**
`-(c₁/2)F_* - (c₂/2)D_zF_*` plus the **reference forcing** `-μF_* + μD_zF_*`. -/
theorem forcing_split (α μ : ℝ) (M : ModState) (z θ s : ℝ) (hμ : 1 + μ ≠ 0) :
    -(M.kappa s - 1) * Work.Construction.Fstar α z θ
      - (M.kappa s * M.b s - 1) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    = -(M.c1 μ s / 2) * Work.Construction.Fstar α z θ
      - (M.c2 μ s / 2) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      + (-μ * Work.Construction.Fstar α z θ
          + μ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := by
  have h1 : M.c1 μ s / 2 = M.kappa s - kappaStar μ := M.c1_sub μ s
  have h2 : M.c2 μ s / 2 = M.kappa s * M.b s - kappaStar μ * bStar μ := M.c2_sub μ s
  have hkb : kappaStar μ * bStar μ = 1 - μ := kappaStar_mul_bStar μ hμ
  rw [h1, h2, hkb, kappaStar_eq]
  ring

end ModState

/-! ## The scales recovered from the rates -/

/-- The **amplitude scale** `λ̄(s) = e^{-s}`: the normalisation `s = -ln λ̄`, `λ̄(0) = 1`. -/
def amp (s : ℝ) : ℝ := Real.exp (-s)

/-- The **space scale** `μ̄(s) = exp(-∫₀^s b)`, so that `d ln μ̄/ds = -b`, i.e. `∂_s z = b z` at
fixed `R` (`Work.Stability.space_deriv`). -/
def space (M : ModState) (s : ℝ) : ℝ := Real.exp (-(∫ u in (0 : ℝ)..s, M.b u))

theorem amp_apply (s : ℝ) : amp s = Real.exp (-s) := rfl

theorem space_apply (M : ModState) (s : ℝ) :
    space M s = Real.exp (-(∫ u in (0 : ℝ)..s, M.b u)) := rfl

theorem amp_pos (s : ℝ) : 0 < amp s := Real.exp_pos _

theorem space_pos (M : ModState) (s : ℝ) : 0 < space M s := Real.exp_pos _

theorem amp_ne_zero (s : ℝ) : amp s ≠ 0 := ne_of_gt (amp_pos s)

theorem space_ne_zero (M : ModState) (s : ℝ) : space M s ≠ 0 := ne_of_gt (space_pos M s)

theorem amp_deriv (s : ℝ) : HasDerivAt amp (-(amp s)) s := by
  have h : HasDerivAt (fun u : ℝ => -u) (-1) s := hasDerivAt_neg s
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-s) * (-1)) s := h.exp
  have h3 : Real.exp (-s) * (-1) = -(amp s) := by rw [amp]; ring
  rw [h3] at h2
  exact h2

/-- The rate relation `μ̄' = -b·μ̄`. -/
theorem space_deriv (M : ModState) (hb : Continuous M.b) (s : ℝ) :
    HasDerivAt (space M) (-(M.b s * space M s)) s := by
  have h : HasDerivAt (fun u : ℝ => ∫ x in (0 : ℝ)..u, M.b x) (M.b s) s :=
    intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable 0 s)
      hb.aestronglyMeasurable.stronglyMeasurableAtFilter hb.continuousAt
  have h2 : HasDerivAt (fun u : ℝ => -(∫ x in (0 : ℝ)..u, M.b x)) (-(M.b s)) s := h.neg
  have h3 : HasDerivAt (fun u : ℝ => Real.exp (-(∫ x in (0 : ℝ)..u, M.b x)))
      (Real.exp (-(∫ x in (0 : ℝ)..s, M.b x)) * (-(M.b s))) s := h2.exp
  have h4 : Real.exp (-(∫ x in (0 : ℝ)..s, M.b x)) * (-(M.b s))
      = -(M.b s * space M s) := by rw [space]; ring
  rw [h4] at h3
  exact h3

/-! ## The rescaling maps -/

namespace ModState

/-- `scaleZ M s R = R/μ̄(s)`: the self-similar radial variable `z` of a physical radial variable
`R = ρ^α` at self-similar time `s`. -/
def scaleZ (M : ModState) (s : ℝ) (R : ℝ) : ℝ := R / space M s

theorem scaleZ_apply (M : ModState) (s R : ℝ) : M.scaleZ s R = R / space M s := rfl

theorem scaleZ_pos {M : ModState} {s R : ℝ} (hR : 0 < R) : 0 < M.scaleZ s R :=
  div_pos hR (space_pos M s)

theorem scaleZ_mul_space (M : ModState) (s R : ℝ) : space M s * M.scaleZ s R = R := by
  rw [scaleZ, mul_div_cancel₀ _ (space_ne_zero M s)]

/-- The **rescaled profile** of a physical vorticity field `Ω`: `f(z,θ,s) = λ̄(s) Ω(μ̄(s)z,θ,s)`.
The defining relation is `Ω(R,θ,s) = λ̄(s)^{-1} f(R/μ̄(s),θ,s)`. -/
def rescaled (M : ModState) (Ω : F3) : F3 :=
  fun z θ s => amp s * Ω (space M s * z) θ s

theorem rescaled_apply (M : ModState) (Ω : F3) (z θ s : ℝ) :
    M.rescaled Ω z θ s = amp s * Ω (space M s * z) θ s := rfl

/-- The inverse relation: the physical profile is `λ̄^{-1}` times the rescaled one. -/
theorem rescaled_spec (M : ModState) {Ω : F3} {R θ s : ℝ} :
    (amp s)⁻¹ * M.rescaled Ω (M.scaleZ s R) θ s = Ω R θ s := by
  rw [rescaled_apply, scaleZ, mul_div_cancel₀ _ (space_ne_zero M s),
    inv_mul_cancel_left₀ (amp_ne_zero s)]

end ModState

/-- The map on `ℝ³`: `x ↦ Rc α x / μ̄(s) = ρ(x)^α/μ̄(s)` (`Work.Cyl.Rc`). -/
def scaleZx (α : ℝ) (M : ModState) (s : ℝ) (x : Work.Cyl.R3) : ℝ :=
  Work.Cyl.Rc α x / space M s

theorem scaleZx_apply (α : ℝ) (M : ModState) (s : ℝ) (x : Work.Cyl.R3) :
    scaleZx α M s x = Work.Cyl.Rc α x / space M s := rfl

/-! ## The perturbation `g` -/

/-- The full profile `F = F_* + g` of the modulation. -/
def Ftot (α : ℝ) (g : F3) (s : ℝ) : F2 :=
  fun z θ => Work.Construction.Fstar α z θ + g z θ s

/-- The perturbation `g = F - F_*` of a rescaled profile `f`. -/
def gPert (α : ℝ) (f : F3) : F3 :=
  fun z θ s => f z θ s - Work.Construction.Fstar α z θ

theorem Ftot_apply (α : ℝ) (g : F3) (s z θ : ℝ) :
    Ftot α g s z θ = Work.Construction.Fstar α z θ + g z θ s := rfl

theorem gPert_apply (α : ℝ) (f : F3) (z θ s : ℝ) :
    gPert α f z θ s = f z θ s - Work.Construction.Fstar α z θ := rfl

theorem Ftot_gPert (α : ℝ) (f : F3) : ∀ z θ s, Ftot α (gPert α f) s z θ = f z θ s := by
  intro z θ s
  simp only [Ftot, gPert]; ring

theorem gPert_Ftot (α : ℝ) (g : F3) :
    ∀ z θ s, gPert α (fun z θ s => Ftot α g s z θ) z θ s = g z θ s := by
  intro z θ s
  simp only [Ftot, gPert]; ring

/-! ## The orthogonality conditions -/

/-- **The `L₁₂(·)(0)`-orthogonality condition** `OrthL12`: `L₁₂(g(·,·,s))(0) = 0` for every `s`.
This is the condition (tex 1362-1369, 1567-1568) that makes the projector `𝕡` of `𝓛_Γ^T` preserve
the class, and that St2 propagates from the initial time. -/
def OrthL12 (g : F3) : Prop := ∀ s, Work.Construction.L12 (slice g s) 0 = 0

/-- **Quadratic vanishing at `z = 0`**: `g` and `∂_z g` vanish on `{z = 0}` (tex 1355-1357).
This is exactly the `hz0` hypothesis of `Work.Spaces.SmoothCompact_HkInf` (and of
`Work.Stability.ZcutSmoothCompact`) for the perturbation `g` itself, hence what places the
*cut-off* perturbation and each of its `D`-derivatives in the weighted spaces `ℋ^k`.

**Caution.**  The *full* profile `F = F_* + g` does **not** satisfy this: `F_* =
α(Γ/c)·2z/(1+z)²` vanishes only *linearly* at `z = 0`, so `∂_z(F_*+g)(0,θ) = 2αΓ(θ)/c ≠ 0`
(`QuadVanish_of_quadVanish` below records the correct transfer, which is only about `g`). -/
def QuadVanish (g : F3) : Prop :=
  (∀ θ s, g 0 θ s = 0) ∧ (∀ θ s, Work.Spaces.pz (slice g s) 0 θ = 0)

/-- `QuadVanish` is the `hz0` hypothesis of `Work.Spaces.SmoothCompact_HkInf` for the
perturbation itself. -/
theorem QuadVanish_of_quadVanish {g : F3} (h : QuadVanish g) (s : ℝ) :
    ∀ θ ∈ Work.Spaces.Iθ, slice g s 0 θ = 0 ∧ Work.Spaces.pz (slice g s) 0 θ = 0 :=
  fun θ _ => ⟨h.1 θ s, h.2 θ s⟩

/-! ## The dynamical rescaled vorticity equation -/

/-- The left hand side of the **dynamical rescaled vorticity equation** at `(z,θ,s)`:
`κ(s)[∂_s f + f + b(s) D_z f] + UVR α f φ`.  For constant `(κ,b) = (κ*,b*)` and `∂_s f = 0` this
is the stationary left hand side of `Work.Construction.StatEqF` with `(1+μ,1+λ) = (κ*,b*)`. -/
def dynLHS (α : ℝ) (M : ModState) (f φ : F3) (z θ s : ℝ) : ℝ :=
  M.kappa s * (deriv (fun u => f z θ u) s + f z θ s
      + M.b s * Work.Spaces.Dz (slice f s) z θ)
    + Work.Construction.UVR α (slice f s) (slice φ s) z θ

/-- **The dynamical rescaled vorticity equation**: the Euler equations in self-similar
variables, with time-dependent rates `(κ,b)`, after dividing by `λ̄²`,

  `κ(s)[∂_s f + f + b(s) D_z f] + UVR α f φ = 0`   on the open quadrant. -/
def DynEq (α : ℝ) (M : ModState) (f φ : F3) : Prop :=
  ∀ z θ s, (z, θ) ∈ Work.Construction.Qd → dynLHS α M f φ z θ s = 0

/-- The same equation with the `s`-derivative recorded as a `HasDerivAt` statement (the form in
which a solution of the Euler equations produces it). -/
def DynEqHasDeriv (α : ℝ) (M : ModState) (f φ : F3) : Prop :=
  ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
    HasDerivAt (fun u => f z θ u)
      (-(f z θ s + M.b s * Work.Spaces.Dz (slice f s) z θ
        + (M.kappa s)⁻¹ * Work.Construction.UVR α (slice f s) (slice φ s) z θ)) s

/-! ## The physical (self-similar) vorticity equation -/

/-- **The self-similar vorticity equation** (tex 1319), with the paper's `1/2` time dilation:
`(1/2)∂_tΩ + U(Ψ)∂_θΩ + V(Ψ)·αR∂_RΩ = ℛ(Ψ)Ω`.  Here `U, V, ℛ` are the operators of
(Relations) evaluated on the slice `Ψ(·,·,s)` (`Work.Construction.Uop/Vop/Rop`). -/
def SelfSimEuler (α : ℝ) (Ω Ψ : F3) : Prop :=
  ∀ R θ t, (R, θ) ∈ Work.Construction.Qd →
    (1 / 2) * deriv (fun u => Ω R θ u) t
      + Work.Construction.Uop α (slice Ψ t) R θ * deriv (fun θ' => Ω R θ' t) θ
      + Work.Construction.Vop (slice Ψ t) R θ
          * (α * R * deriv (fun R' => Ω R' θ t) R)
      - Work.Construction.Rop α (slice Ψ t) R θ * Ω R θ t = 0

namespace ModState

/-- The **physical image** of a rescaled family: `Ω(R,θ,s) = λ̄(s)^{-1} f(R/μ̄(s),θ,s)`
(`λ̄ = amp`, `μ̄ = space`).  This is the inverse of `rescaled`, written as a `F3`. -/
def physProfile (M : ModState) (f : F3) : F3 :=
  fun R θ s => (amp s)⁻¹ * f (R / space M s) θ s

theorem physProfile_apply (M : ModState) (f : F3) (R θ s : ℝ) :
    M.physProfile f R θ s = (amp s)⁻¹ * f (R / space M s) θ s := rfl

/-- The physical profile at the self-similar coordinate `z`: `Ω(μ̄ z, θ, s) = λ̄(s)^{-1}f(z,θ,s)`. -/
theorem physProfile_at (M : ModState) (f : F3) (z θ s : ℝ) :
    M.physProfile f (space M s * z) θ s = (amp s)⁻¹ * f z θ s := by
  rw [physProfile_apply, mul_div_cancel_left₀ _ (space_ne_zero M s)]

end ModState

/-- **The self-similar vorticity equation in the `s`-parametrisation**: the paper's (tex 1319)
`(1/2)∂_tΩ + U(Ψ)∂_θΩ + V(Ψ)αR∂_RΩ = ℛ(Ψ)Ω`, with `∂_tΩ` expressed through `∂_sΩ` via the
modulation (`∂_t = κ(s)·λ̄(s)^{-1}·∂_s`, since `ds/dt = κλ̄^{-1}` and `κ = -λ̄'` is the amplitude
rate of the state).  Substituting the ansatz `Ω = λ̄^{-1}f(R/μ̄,θ,s)` turns this equation into
`DynEq` (`Work.Stability.dynEq_of_selfSimEulerS`). -/
def SelfSimEulerS (α : ℝ) (M : ModState) (Ω Ψ : F3) : Prop :=
  ∀ R θ s, (R, θ) ∈ Work.Construction.Qd →
    (1 / 2) * M.kappa s * (amp s)⁻¹ * deriv (fun u => Ω R θ u) s
      + Work.Construction.Uop α (slice Ψ s) R θ * deriv (fun θ' => Ω R θ' s) θ
      + Work.Construction.Vop (slice Ψ s) R θ
          * (α * R * deriv (fun R' => Ω R' θ s) R)
      - Work.Construction.Rop α (slice Ψ s) R θ * Ω R θ s = 0

/-! ## The `g`-equation -/

/-- The right hand side of the **dynamical `g`-equation**:
`-(κ-1)F_* - (κb-1)D_zF_* + AK·L₁₂(Transport g)(0) + N₀ + N + N_*`, evaluated at the slice `s`.
This is the exact right hand side produced by substituting `f = F_*+g` into `DynEq`; St2 proves
the identity and rewrites the forcing through `c₁, c₂`. -/
def gDynRHS (α : ℝ) (M : ModState) (g φ : F3) (z θ s : ℝ) : ℝ :=
  -(M.kappa s - 1) * Work.Construction.Fstar α z θ
    - (M.kappa s * M.b s - 1) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    + Work.Construction.AK α z θ
        * Work.Construction.L12 (Work.Coercivity.Transport (slice g s)) 0
    + Work.Construction.N0 α (Ftot α g s) (slice g s) z θ
    + Work.Construction.N α (Ftot α g s) (slice φ s) z θ
    + Work.Construction.Nstar (M.kappa s - 1) (M.b s - 1) (slice g s) z θ

/-- **The dynamical `g`-equation** as a predicate: `κ ∂_s g + 𝓛_Γ^T(g) = gDynRHS`. -/
def GEquation (α : ℝ) (M : ModState) (g φ : F3) : Prop :=
  ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
    M.kappa s * deriv (fun u => g z θ u) s
      + Work.Coercivity.LGammaT α (slice g s) z θ = gDynRHS α M g φ z θ s

/-- The `g`-equation with an extra *far-field* term: the compactly supported solution does not
satisfy the rescaled equation in the far region, and the deficit is `Far`.  This is the equation
St2 derives and St3 bootstraps with; `Far` is the single named hypothesis of the layer (see
`NOTES.md`). -/
def GEquationFar (α : ℝ) (M : ModState) (g φ : F3) (Far : F3) : Prop :=
  ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
    M.kappa s * deriv (fun u => g z θ u) s
      + Work.Coercivity.LGammaT α (slice g s) z θ = gDynRHS α M g φ z θ s + Far z θ s

/-- The **reference forcing** of the `g`-equation: the part of `gDynRHS` that survives at the
reference rates, `-μF_* + μD_zF_* + AK·L₁₂(Transport g)(0)`.  The identity `κ*b* = 1-μ` of the
dictionary turns it into `-2αμ·AK + AK·L₁₂(Transport g)(0)` (`refForcing_eq`), and the modulation
constant is chosen so that this `AK`-coefficient is the paper's `-μ̄`. -/
def refForcing (α : ℝ) (μ : ℝ) (g : F3) (z θ s : ℝ) : ℝ :=
  -μ * Work.Construction.Fstar α z θ + μ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    + Work.Construction.AK α z θ
        * Work.Construction.L12 (Work.Coercivity.Transport (slice g s)) 0

/-- The reference forcing is `-2αμ·AK` plus the `L₁₂(Transport g)(0)` correction: this is the
identity `F_* - D_zF_* = 2α·AK` of tex 1357. -/
theorem refForcing_eq (α μ : ℝ) (g : F3) (z θ s : ℝ) (hα : 0 < α) (hz : -1 < z) :
    refForcing α μ g z θ s
      = -2 * α * μ * Work.Construction.AK α z θ
        + Work.Construction.AK α z θ
            * Work.Construction.L12 (Work.Coercivity.Transport (slice g s)) 0 := by
  have h := Work.Construction.Fstar_sub_DzFstar (α := α) (z := z) (θ := θ) hα hz
  rw [refForcing]
  linear_combination (-μ) * h

/-- The whole `g`-forcing is the *mismatch* plus the *reference forcing*:
`-(κ-1)F_* - (κb-1)D_zF_* + AK·L₁₂(Transport g)(0) = -(c₁/2)F_* - (c₂/2)D_zF_*
 + refForcing`. -/
theorem forcing_split_refForcing (α μ : ℝ) (M : ModState) (g : F3) (z θ s : ℝ)
    (hμ : 1 + μ ≠ 0) :
    -(M.kappa s - 1) * Work.Construction.Fstar α z θ
      - (M.kappa s * M.b s - 1) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      + Work.Construction.AK α z θ
          * Work.Construction.L12 (Work.Coercivity.Transport (slice g s)) 0
    = -(M.c1 μ s / 2) * Work.Construction.Fstar α z θ
      - (M.c2 μ s / 2) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      + refForcing α μ g z θ s := by
  have h := M.forcing_split α μ z θ s hμ
  rw [refForcing]
  linarith [h]

end Work.Stability
