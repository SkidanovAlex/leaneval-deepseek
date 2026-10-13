/-
# The STABILITY layer — **St2: the dynamical `g`-equation and the modulation conditions**

This module (`Submission.Work.Stability.ModEqn`) is St2 of the design
(`NOTES_LEAD_Stability.md`): the *dynamic* `g`-equation obtained by substituting `f = F_* + g`
into the rescaled vorticity equation `DynEq` of St0, together with the two modulation
conditions `(M1)`, `(M2)` of tex 1355-1357 / 1362-1369 and their algebraic form.

## The exact `g`-equation

Write `κ = κ(s)`, `b = b(s)` for the two rates of the state `M` (`Work.Stability.ModState`), and
let `UVR α F Φ = 2U(Φ)∂_θF + 2αV(Φ)D_zF - 2ℛ(Φ)F` (`Work.Construction.UVR`).  Two identities
carry the derivation:

* **`mainLHS_sub_N`** (the "static" identity, tex 1345 without the stationary equation):  for
  *arbitrary* `F, Φ` that admit the paper's decomposition `Φ = Φ̃ + Θ`,
  `(1+μ)F + (1+μ)(1+λ)D_zF + UVR α F Φ = MainLHS α μ lam F - N α F Φ`.
  (The Construction area proves `MainLHS = N` *under* the stationary equation `StatEqF`
  (`MainLHS_eq_N`); the identity above needs no such hypothesis and is what the dynamical
  equation, which does not hold, requires.)  It is the combination of `UVR_sub` with the
  definition of `N`.
* `LGammaT_eq`: `𝓛_Γ(g) - Transport g = 𝓛_Γ^T(g) - AK·L₁₂(Transport g)(0)`.

Applying the first to `F = F_* + g`, with `μ = κ-1`, `λ = b-1`, and feeding it into `DynEq`
gives, after moving `N` to the right and using `MainLHS_explicit` (which expands `MainLHS` in
terms of `g`, `F_*` and the identity `F_* + D_zF_* - (1/α)L₁₂(F_*)F_* = 0`) and
`Transport g = (3/(2α)) sin(2θ)L₁₂(F_*)∂_θ g`,

  **`κ ∂_s g + 𝓛_Γ^T(g) = -(κ-1)F_* - (κb-1)D_zF_* + AK·L₁₂(Transport g)(0) + N₀ + N + N_*`**

(`dyn_gEquation`), which is the paper's `(intermediategeqn)`-plus-`(gEquationFinal)` chain with
time-dependent coefficients.  Splitting the forcing through the mismatch rates
(`forcing_split_refForcing`) turns this into the design's shape

  **`κ ∂_s g + 𝓛_Γ^T(g) = -(c₁/2)F_* - (c₂/2)D_zF_* + refForcing + N₀ + N + N_*`**

(`GEquationC1C2`), where `refForcing = -μF_* + μD_zF_* + AK·L₁₂(Transport g)(0)
= -2αμ·AK + AK·L₁₂(Transport g)(0)` by `F_* - D_zF_* = 2α·AK`.

## The modulation conditions

* **`(M1)` `ModCond1`** — the `L₁₂(·)(0)`-component of the right hand side of the `g`-equation
  vanishes (tex 1366-1369).  Together with the operator identity
  `L₁₂(𝓛_Γ^T g)(0) = -L₁₂(g)(0)` (`L12f_LGammaT_zero`) and the interchange
  `L₁₂(∂_s g_s)(0) = ∂_s L₁₂(g_s)(0)` (`L12f_slice_deriv`) it gives the *modulation ODE* for the
  quantity `s ↦ L₁₂(g(·,·,s))(0)`, hence the propagation of `OrthL12` from the initial time
  (`orthL12_propagates`).
* **`(M2)` `ModCond2`** — the right hand side vanishes to second order at `z = 0` (tex
  1355-1357): this is what fixes the second modulation constant (`λ = -2μ/(1+μ)` in the
  stationary problem) and hence `c₂`.

Both conditions are *linear* in the pair of unknowns `(κ, κb)` — equivalently in
`(c₁, c₂)` — with coefficients that depend on `g` only through the nonlinear terms; the
per-`s` `2×2` algebra is isolated in `Work.Stability.Solve2x2` / `Work.Stability.ModSolve`, with
the `L₁₂`-evaluations of the reference profile `F_*`, `D_zF_*` and `AK` supplying the matrix
(`Work.Construction.L12_AK_eq_one`, `Work.Construction.L12_Fstar_eq`).

## The far-field term

`GEquationWithFar` adds the single *named* term `Far` of the design (the deficit of the cut-off
compactly supported solution, owned by the `StabilityFar` sibling); see `NOTES.md`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Stability.Defs

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

/-! ## The hypotheses of the derivation -/

/-- **The derivation data for the dynamical `g`-equation.**  This bundles the hypotheses that
the Construction area's derivation of `(intermediategeqn)` takes as inputs (its `h2,h3,h5,h6`,
`hDz`, `hpth`, `hL`), now *for the family* `F(·,·,s) = F_* + g(·,·,s)`:

* `h2`, `h3` — the decomposition `Φ = Φ̃ + Θ` is differentiable in `z` and `θ` (with the
  derivatives of `Θ` computed separately);
* `h5`, `h6` — the two derivative evaluations of `Θ = (1/(4α))sin(2θ)L₁₂(F)`, supplied by
  `Work.Construction.pth_Theta_eq` and `Work.Construction.Dz_Theta_eq` (see
  `Work.Stability.ThetaPthFtot`, `Work.Stability.ThetaPzFtot`);

(the four `Φ = Φ̃ + Θ` fields `h2, h3, h5, h6` are restricted to the **open quadrant** `Qd`:
`h5` genuinely needs `z > 0`, since `L₁₂(F_*)` is a Lean-junk `0` for `z ≤ -1` while
`FK(F_*) ≠ 0` there — see the reviewer's counterexample.  `DynGEquation` only consumes them on
`Qd`, where its conclusion lives.)
* `hDz`, `hpth` — the splitting of `D_z` and `∂_θ` over `F = F_* + g` on the *open quadrant*
  (where `z > 0` and `0 < θ < π/2`, so both `F_*`-slices are differentiable), supplied by
  `Work.Stability.PzFstarAdd` / `PthFstarAdd` from differentiability of the slices of `g`;
* `hL` — the splitting of `L₁₂` over `F = F_* + g`, supplied by integrability of the
  `L₁₂`-densities (`Work.Stability.L12Add`). -/
structure GDerivData (α : ℝ) (g φ : F3) : Prop where
  h2 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pz (slice φ s) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α (Ftot α g s) (slice φ s)) z θ
          + Work.Spaces.pz (Work.Construction.Theta α (Ftot α g s)) z θ
  h3 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (slice φ s) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α (Ftot α g s) (slice φ s)) z θ
          + Work.Spaces.pth (Work.Construction.Theta α (Ftot α g s)) z θ
  h5 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      z * Work.Spaces.pz (Work.Construction.Theta α (Ftot α g s)) z θ
        = -(1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.FK (Ftot α g s) z
  h6 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Work.Construction.Theta α (Ftot α g s)) z θ
        = (1 / (2 * α)) * Real.cos (2 * θ) * Work.Construction.L12 (Ftot α g s) z
  hDz : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (fun z θ => Ftot α g s z θ) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz (slice g s) z θ
  hpth : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (fun z θ => Ftot α g s z θ) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth (slice g s) z θ
  hL : ∀ z s, Work.Construction.L12 (fun z θ => Ftot α g s z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 (slice g s) z

/-! ## The modulated form of the `g`-equation -/

/-- **The dynamical `g`-equation with the mismatch rates.**  Same equation as `GEquation`, with
the forcing written as the *mismatch* `-(c₁/2)F_* - (c₂/2)D_zF_*` plus the *reference forcing*
`refForcing`.  This is the form in which the estimates of St3 are applied (the mismatch terms
carry the factor `α` through `|F_*|_{ℋ⁴} = O(α)`). -/
def GEquationC1C2 (α μ : ℝ) (M : ModState) (g φ : F3) : Prop :=
  ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
    M.kappa s * deriv (fun u => g z θ u) s
      + Work.Coercivity.LGammaT α (slice g s) z θ
    = -(M.c1 μ s / 2) * Work.Construction.Fstar α z θ
      - (M.c2 μ s / 2) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      + refForcing α μ g z θ s
      + Work.Construction.N0 α (Ftot α g s) (slice g s) z θ
      + Work.Construction.N α (Ftot α g s) (slice φ s) z θ
      + Work.Construction.Nstar (M.kappa s - 1) (M.b s - 1) (slice g s) z θ

/-- **The modulated `g`-equation with an extra far-field term** (the form St3 bootstraps).
`Far` is the single named hypothesis of the Stability layer. -/
def GEquationWithFar (α μ : ℝ) (M : ModState) (g φ Far : F3) : Prop :=
  ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
    M.kappa s * deriv (fun u => g z θ u) s
      + Work.Coercivity.LGammaT α (slice g s) z θ
    = -(M.c1 μ s / 2) * Work.Construction.Fstar α z θ
      - (M.c2 μ s / 2) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      + refForcing α μ g z θ s
      + Work.Construction.N0 α (Ftot α g s) (slice g s) z θ
      + Work.Construction.N α (Ftot α g s) (slice φ s) z θ
      + Work.Construction.Nstar (M.kappa s - 1) (M.b s - 1) (slice g s) z θ
      + Far z θ s

/-- `GEquation` and `GEquationC1C2` are the same equation (the forcing split). -/
theorem gEquation_iff_c1c2 {α μ : ℝ} {M : ModState} {g φ : F3} (hμ : 1 + μ ≠ 0) :
    GEquation α M g φ ↔ GEquationC1C2 α μ M g φ := by
  have key : ∀ z θ s, gDynRHS α M g φ z θ s
      = -(M.c1 μ s / 2) * Work.Construction.Fstar α z θ
        - (M.c2 μ s / 2) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        + refForcing α μ g z θ s
        + Work.Construction.N0 α (Ftot α g s) (slice g s) z θ
        + Work.Construction.N α (Ftot α g s) (slice φ s) z θ
        + Work.Construction.Nstar (M.kappa s - 1) (M.b s - 1) (slice g s) z θ := by
    intro z θ s
    have h := forcing_split_refForcing α μ M g z θ s hμ
    simp only [gDynRHS]
    linarith [h]
  constructor
  · intro h z θ s hzθ
    have h1 := h z θ s hzθ
    rw [key z θ s] at h1
    exact h1
  · intro h z θ s hzθ
    have h1 := h z θ s hzθ
    rw [key z θ s]
    exact h1

/-! ## The modulation conditions -/

/-- **Modulation condition `(M1)`** (tex 1366-1369): the `L₁₂(·)(0)`-component of the right hand
side of the `g`-equation vanishes for every `s`.  This is the condition that keeps `L₁₂(g)(0)`
at its initial value `0` (the paper's `μ̄ := L₁₂(N₀)(0) + L₁₂(N)(0)` is exactly the choice of
modulation that makes it hold to leading order). -/
def ModCond1 (α : ℝ) (M : ModState) (g φ : F3) : Prop :=
  ∀ s, Work.Construction.L12 (fun z θ => gDynRHS α M g φ z θ s) 0 = 0

/-- **Modulation condition `(M2)`** (tex 1355-1357): the right hand side of the `g`-equation
vanishes to second order at `z = 0`.  This is what fixes the second modulation constant
(`λ = -2μ/(1+μ)` in the stationary problem), hence `b` and `c₂`; it is the condition that makes
`L₁₂(g)(0) = 0` propagate *and* keeps `g` quadratically vanishing, so that `F = F_*+g` lies in
the weighted spaces `ℋ^k`.  It is phrased as: the right hand side, divided by `z²`, tends to `0`
as `z → 0⁺`, uniformly in `θ`. -/
def ModCond2 (α : ℝ) (M : ModState) (g φ : F3) : Prop :=
  ∀ s, ∀ ε > 0, ∃ δ > 0, ∀ z, 0 < z → z < δ → ∀ θ ∈ Work.Spaces.Iθ,
    |gDynRHS α M g φ z θ s| ≤ ε * z ^ 2

/-- Both modulation conditions together. -/
def ModCond (α : ℝ) (M : ModState) (g φ : F3) : Prop :=
  ModCond1 α M g φ ∧ ModCond2 α M g φ

end Work.Stability
