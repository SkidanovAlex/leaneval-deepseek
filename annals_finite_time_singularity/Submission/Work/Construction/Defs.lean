/-
# The CONSTRUCTION area: the modulation / fixed-point chapter of Elgindi's paper

This directory (`Submission/Work/Construction/`) formalises §Modulation of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), 1--70,

i.e. the self-similar ansatz and its modulation (`Papers/elgindi/Classical_Euler_arXiv_2.tex`,
tex lines 1317--1578): the decomposition `F = F_* + g`, the modulation constants
`μ, lam` (and `μ̄`), the `g`-equation `gEquationFinal` (tex 1369), the a-priori estimate on
the `ℋ⁴` inner product of that equation with `g` (Propositions `N0Estimate`, `NEstimate`,
`N*Estimate`, `innerproductestimate`), and the "fake time" fixed-point/existence argument
(tex 1549--1578).

## Conventions

Functions of the self-similar variables are curried, `f : ℝ → ℝ → ℝ`, applied as `f z θ`,
and all integrals are over `Iz × Iθ = [0,∞) × [0,π/2]` with the measure `dz dθ` — the
Warning of §Notation of the paper: **not** `z dz dθ`.  This is the convention of
`Submission/Work/Spaces`, `Submission/Work/FM`, `Submission/Work/Elliptic` and
`Submission/Work/Coercivity`, whose vocabulary (`Spaces.HkSq`, `Spaces.HkNorm`,
`Spaces.WlInf`, `FM.L12`, `Coercivity.LGammaT`, …) is reused here.

* `z` is the self-similar radial variable `z = R/(1-(1+μ)t)^{1+lam}` (the paper's `R` in
  §Elliptic and `z` in §Modulation); `D_z f = z ∂_z f` is `Spaces.Dz`, `D_θ f = sin(2θ)∂_θ f`
  is `Spaces.Dth`.
* `Γ(θ) = (sin θ cos²θ)^{α/3}` is `Spaces.Gam α`, `K(θ) = 3 sin θ cos²θ` is `Spaces.K`, and
  `c = ∫_0^{π/2} Γ K = Spaces.c α`.
* The modulation constants `μ` and `lam` are kept as **free real parameters** in every
  statement (the Stability layer reuses this chapter with time-dependent coefficients);
  the paper's choice `lam = -2μ/(1+μ)` is the definition `lamfun μ` and its consequences are
  lemmas, not built into the definitions.
* `μ̄` is the paper's `L₁₂(N₀)(0) + L₁₂(N)(0)` and `μ` the paper's
  `(1/(2α))(L₁₂(N₀)(0)+L₁₂(N)(0)) - (1/(2α))L₁₂(3 D_θ g/(1+z))(0)`.

## Discrepancies with the LaTeX source, resolved here

* `Nstar` is `-μ g - (μ+lam+μλ) z ∂_z g`.  The paper's display `\eqref{N*}`
  (`N_* = -μg - (μ+lam+μλ)g`) drops the `z∂_z`; the definition is forced by the derivation
  (the linear part of `-μF-(μ+lam+μλ)z∂_zF` in `g`), and it is what the paper's own estimate
  `|(N_*,g)| ≤ C|μ|(|(g,g)|+|(g,z∂_zg)|)` uses.  See `Nstar_expand`.
* The last two terms of `N` (tex `\eqref{N}`) are written in the paper with coefficients
  `-α` and `-2α`; the exact expansion of `U, V, ℛ` on `Φ = Φ̃ + (1/(4α))sin(2θ)L₁₂(F)`
  (with `z∂_z L₁₂(F) = -(F,K)`) gives the coefficients `-1/2` and `-1` (see `UVR_sub`).
  We use the exact form; the two differ by the factor `2α ≤ 1`, so every estimate below
  holds verbatim for the paper's version as well, with a universal constant adjusted.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Defs
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## The operator `L₁₂` and the angular moment `(F,K)` -/

/-- The paper's integral operator
`L₁₂(f)(z) = ∫_z^∞ ∫_0^{π/2} K(θ) f(r,θ)/r dθ dr` with `K = Spaces.K`.  This is
`Work.FM.L12 Spaces.K` (i.e. `Work.Elliptic.L12`, by `L12_eq_Elliptic`). -/
def L12 (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := Work.FM.L12 Work.Spaces.K f z

/-- The angular density `∫_0^{π/2} K(θ) f(s,θ)/s dθ` of `L₁₂`. -/
def L12dens (f : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := Work.FM.L12dens Work.Spaces.K f s

/-- The angular moment `(F,K)_{L²_θ}(z) = ∫_0^{π/2} F(z,θ) K(θ) dθ` of the paper.  It is
`z ∂_z L₁₂(F)(z) = - (F,K)_{L²_θ}(z)` (see `mul_deriv_L12`). -/
def FK (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, F z θ * Work.Spaces.K θ

/-- `s2 θ = sin(2θ)`, the angular factor of `D_θ` and of the transport term. -/
def s2 (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- `c2m θ = cos(2θ) - sin²θ`, the angular coefficient of the second and sixth terms of
`N₀` and of the transport term of `𝓛_Γ^T`. -/
def c2m (θ : ℝ) : ℝ := Real.cos (2 * θ) - Real.sin θ ^ 2

/-- The **open quadrant** `(0,∞) × (0,π/2)`: the set on which the identities of
§Modulation hold (the paper's identities involve `tan θ` and `1/cos θ`, which Lean
totalises at `θ = π/2`; the complement of the open quadrant is Lebesgue-null, so every
integral and every `ℋ^k`-norm is unaffected). -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

@[simp] theorem s2_eq (θ : ℝ) : s2 θ = Real.sin (2 * θ) := rfl
@[simp] theorem c2m_eq (θ : ℝ) : c2m θ = Real.cos (2 * θ) - Real.sin θ ^ 2 := rfl

/-! ## The operators `U`, `V`, `ℛ` of the self-similar vorticity equation -/

/-- `U(Ψ) := -3Ψ - α z ∂_zΨ` (paper (Relations), tex 1320 / (PhitoU), tex 1378): the
coefficient of `∂_θΩ` in the self-similar vorticity equation.  (Same definition as
`Work.Elliptic.Uop`; see `Uop_eq`.) -/
def Uop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -3 * Ψ z θ - α * z * Work.Spaces.pz Ψ z θ

/-- `V(Ψ) := ∂_θΨ - tan θ · Ψ`: the coefficient of `α z ∂_zΩ`. -/
def Vop (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ

/-- `ℛ(Ψ) := (1/cos θ)(2 sin θ · Ψ + α sin θ · z ∂_zΨ + cos θ · ∂_θΨ)`: the coefficient of
`Ω` in the self-similar vorticity equation. -/
def Rop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
    + Real.cos θ * Work.Spaces.pth Ψ z θ) / Real.cos θ

/-- The combination of the vorticity equation in which the coefficients `U, V, ℛ` are
evaluated at `Φ`, i.e. `2U(Φ)∂_θF + 2αV(Φ)D_zF - 2ℛ(Φ)F`. -/
def UVR (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * Uop α Φ z θ * Work.Spaces.pth F z θ
    + 2 * α * Vop Φ z θ * Work.Spaces.Dz F z θ - 2 * Rop α Φ z θ * F z θ

/-! ## The self-similar ansatz -/

/-- The self-similar variable `z = R/(1-(1+μ)t)^{1+lam}`. -/
def zvar (μ lam R t : ℝ) : ℝ := R / (1 - (1 + μ) * t) ^ (1 + lam)

/-- The amplitude `(1-(1+μ)t)^{-1}` of the self-similar ansatz. -/
def scalefac (μ t : ℝ) : ℝ := (1 - (1 + μ) * t)⁻¹

/-- The self-similar ansatz for the vorticity,
`Ω(R,θ,t) = (1-(1+μ)t)^{-1} F(R/(1-(1+μ)t)^{1+lam}, θ)`. -/
def OmegaAns (μ lam : ℝ) (F : ℝ → ℝ → ℝ) (R θ t : ℝ) : ℝ :=
  scalefac μ t * F (zvar μ lam R t) θ

/-- The self-similar ansatz for the stream function,
`Ψ(z,θ,t) = (1-(1+μ)t)^{-1} Φ(z,θ)`. -/
def PsiAns (μ : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ t : ℝ) : ℝ := scalefac μ t * Φ z θ

/-- The stationary equation for `F` (paper tex 1330): the self-similar vorticity equation
`(1/2)∂_tΩ + U(Ψ)∂_θΩ + V(Ψ)αR∂_RΩ = ℛ(Ψ)Ω` for the ansatz, with every term moved to the
left: `(1+μ)F + (1+μ)(1+lam)z∂_zF + UVR(F,Φ) = 0`. -/
def StatEqF (α μ lam : ℝ) (F Φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ, (1 + μ) * F z θ + (1 + μ) * (1 + lam) * Work.Spaces.Dz F z θ
    + UVR α F Φ z θ = 0

/-- The stationary equation for `Φ` (paper (PolarBSLFinal), tex 1332): the self-similar
Biot--Savart law `ℒ(Φ) = F`.  This is `Work.Elliptic.bslOp α Φ = F`. -/
def StatEqPhi (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ, Work.Elliptic.bslOp α Φ z θ = F z θ

/-! ## The profile `F_*` and the singular part `Θ` -/

/-- The profile `F_*(z,θ) = α (Γ(θ)/c) 2z/(1+z)²` of the paper (tex 1334). -/
def Fstar (α : ℝ) (z θ : ℝ) : ℝ :=
  α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar z

/-- The profile `(Γ(θ)/c) 2z²/(1+z)³` which is the correction of the projector `𝕡` of
`𝓛_Γ^T`; it is the radial derivative combination `-(μ F_* - μ z∂_zF_*)/(2αμ)`. -/
def AK (α : ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)

/-- The singular part `Θ = (1/(4α)) sin(2θ) L₁₂(F)` of the stream function `Φ`; the
elliptic estimates are for `Φ - Θ` (`Work.Elliptic.EllResid = ΦTil`). -/
def Theta (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 / (4 * α)) * s2 θ * L12 F z

/-- `Φ - Θ`: the quantity the elliptic estimates (Theorem `RemovingL12`) control. -/
def PhiTil (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Φ z θ - Theta α F z θ

/-- The full profile `F = F_* + g` of the modulation. -/
def Ftot (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Fstar α z θ + g z θ

/-! ## The nonlinear terms `N₀`, `N`, `N_*` (tex (N0)--(N*)) -/

/-- The term `N₀` of the paper (tex `\eqref{N0}`): everything that is quadratic in
`(F_*, g)`, with `F = F_* + g` the full profile and `g` the modulation.  Recall
`L₁₂(F_*) = 2α/(1+z)` (`L12_Fstar`). -/
def N0 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth (Fstar α) z θ
    - c2m θ * L12 (Fstar α) z * Work.Spaces.Dz (Fstar α) z θ
    + (1 / α) * L12 g z * g z θ
    + (3 / (2 * α)) * s2 θ * L12 g z * Work.Spaces.pth F z θ
    - c2m θ * L12 g z * Work.Spaces.Dz F z θ
    - c2m θ * L12 (Fstar α) z * Work.Spaces.Dz g z θ

/-- The term `N` of the paper (tex `\eqref{N}`): the elliptic correction
`Φ̃ = Φ - (1/(4α))sin(2θ)L₁₂(F)` transported by `U, V` and observed by `ℛ`, together with
the two angular-moment terms.  **Note**: the coefficients `-1/2` and `-1` of the last two
terms are the exact ones (the paper displays `-α` and `-2α`); see the module docstring and
`UVR_sub`. -/
def N (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * Rop α (PhiTil α F Φ) z θ * F z θ
    - 2 * Uop α (PhiTil α F Φ) z θ * Work.Spaces.pth F z θ
    - 2 * α * Vop (PhiTil α F Φ) z θ * Work.Spaces.Dz F z θ
    - (1 / 2) * s2 θ * FK F z * Work.Spaces.pth F z θ
    - Real.sin θ ^ 2 * FK F z * F z θ

/-- The term `N_*` of the paper (tex `\eqref{N*}`): the linear part of
`-μF - (μ+lam+μλ)z∂_zF` in `g`, with the modulation constants `μ, lam` free.  With the paper's
choice `lam = -2μ/(1+μ)` this collapses to `-μ g` (`Nstar_at_lamfun`). -/
def Nstar (μ lam : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -μ * g z θ - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ

/-- The paper's `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)` (tex 1366). -/
def mubar (N0v Nv : ℝ → ℝ → ℝ) : ℝ := L12 N0v 0 + L12 Nv 0

/-- The paper's modulation constant (tex 1380)
`μ = (1/(2α))(L₁₂(N₀)(0)+L₁₂(N)(0)) - (1/(2α))L₁₂(3 D_θ g/(1+z))(0)`. -/
def mufun (α : ℝ) (N0v Nv g : ℝ → ℝ → ℝ) : ℝ :=
  (1 / (2 * α)) * (L12 N0v 0 + L12 Nv 0)
    - (1 / (2 * α)) * L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0

/-- The paper's choice `lam = -2μ/(1+μ)` of the second modulation constant (tex 1356). -/
def lamfun (μ : ℝ) : ℝ := -2 * μ / (1 + μ)

/-! ## The `g`-equation -/

/-- The right hand side of the `g`-equation `\eqref{gEquationFinal}` (tex 1369). -/
def gRHS (α μ lam : ℝ) (F Φ g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -mubar (N0 α F g) (N α F Φ) * AK α z θ
    + N0 α F g z θ + N α F Φ z θ + Nstar μ lam g z θ

/-- **The `g`-equation `\eqref{gEquationFinal}`** (tex 1369):
`𝓛_Γ^T(g) = μ̄ (Γ/c) 2z²/(1+z)³ + N₀ + N + N_*`, i.e. `g` is a stationary solution of the
modulation problem.  Here `F = F_* + g` is the full profile and `Φ` the corresponding stream
function; the fields `Φ` and `F` are kept as arguments (with `F = F_*+g` supplied as a
hypothesis by the callers) so that the statement composes with the elliptic estimates. -/
def IsGSol (α μ lam : ℝ) (F g Φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ, (z, θ) ∈ Qd → Work.Coercivity.LGammaT α g z θ = gRHS α μ lam F Φ g z θ

/-- The left hand side display of tex line 1345,
`(1+μ)F + (1+μ)(1+lam)D_zF - (1/α)L₁₂(F)F - (3/(2α))sin(2θ)L₁₂(F)∂_θF
 + (cos 2θ - sin²θ)L₁₂(F)D_zF`. -/
def MainLHS (α μ lam : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 + μ) * F z θ + (1 + μ) * (1 + lam) * Work.Spaces.Dz F z θ
    - (1 / α) * L12 F z * F z θ
    - (3 / (2 * α)) * s2 θ * L12 F z * Work.Spaces.pth F z θ
    + c2m θ * L12 F z * Work.Spaces.Dz F z θ

/-! ## The inner product on `ℋ⁴` consumed by the a-priori estimate -/

/-- An admissible inner product on `ℋ⁴` for the a-priori estimate of §Modulation: the
paper's inductively constructed `(·,·)_{ℋ⁴}` (`Work.Coercivity.IsHkIP`), together with the
Cauchy--Schwarz bound `|(f,g)_{ℋ⁴}| ≤ |f|_{ℋ⁴}|g|_{ℋ⁴}` which is used whenever the
estimate of a nonlinear term is paired with `g`. -/
structure IsH4IP (α : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) : Prop where
  /-- `IP` is an admissible inner product on `ℋ⁴` in the sense of the paper: it dominates
  the `ℋ⁴` norm squared and `𝓛_Γ^T` is coercive for it. -/
  isHkIP : Work.Coercivity.IsHkIP α 4 IP
  /-- Cauchy--Schwarz for `IP` against the `ℋ⁴` norm. -/
  cs : ∀ f g : ℝ → ℝ → ℝ,
    |IP f g| ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g
  /-- `IP` is additive in its second argument. -/
  add_snd : ∀ (f g₁ g₂ : ℝ → ℝ → ℝ), IP f (g₁ + g₂) = IP f g₁ + IP f g₂
  /-- `IP` is additive in its first argument. -/
  add_fst : ∀ (f₁ f₂ g : ℝ → ℝ → ℝ), IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `IP` is `ℝ`-homogeneous in its first argument. -/
  smul_fst : ∀ (c : ℝ) (f g : ℝ → ℝ → ℝ), IP (fun z θ => c * f z θ) g = c * IP f g
  /-- `IP` only depends on the first argument through its values on the open quadrant `Qd`
  (which is co-null in the domain of integration `Iz × Iθ`). -/
  congr_qd : ∀ (f f' g : ℝ → ℝ → ℝ),
    (∀ z θ, (z, θ) ∈ Qd → f z θ = f' z θ) → IP f g = IP f' g

/-! ## The "fake time" evolution equation -/

/-- The family `F(τ) = F_* + g(·,·,τ)` of full profiles along the fake-time flow. -/
def Ftau (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Fstar α z θ + g z θ τ

/-- The fake-time derivative `∂_τ g(·,·,τ)`. -/
def gdot (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => deriv (fun s => g z θ s) τ

/-- The fake-time equation `\eqref{gequationtime}` (tex 1559) for the family
`g(·,·,τ)`: `∂_τ g + 𝓛_Γ^T(g) = -(L₁₂(N₀)(0)+L₁₂(N)(0))AK + N₀ + N + N_*`, with the
modulation constants `μ, lam` (free parameters) and with `N₀, N, N_*` evaluated on
`F(τ) = F_* + g(τ)` and the corresponding stream function `Φ(·,·,τ)`.  The `τ`-dependent
`μ̄` is the paper's dynamical choice `L₁₂(N₀)(0,τ)+L₁₂(N)(0,τ)`. -/
def IsTimeGSol (α μ lam : ℝ) (Φ : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ τ, (z, θ) ∈ Qd → HasDerivAt (fun s => g z θ s)
    (-(Work.Coercivity.LGammaT α (fun z θ => g z θ τ) z θ)
      + gRHS α μ lam (Ftau α g τ) (fun z θ => Φ z θ τ) (fun z θ => g z θ τ) z θ) τ
