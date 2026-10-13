/-
# The coercivity chapter of Elgindi's finite-time singularity paper

This directory (`Submission/Work/Coercivity/`) formalizes §"Linearization of the
Fundamental Model in Self-Similar Variables" and §"Linearization with angular
transport" of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), 1--70,

(`Papers/elgindi/Classical_Euler_arXiv_2.tex`, lines 475--708).

## Conventions

Functions of the self-similar variables `(z,θ)` are curried functions
`f : ℝ → ℝ → ℝ`, as in `Submission/Work/Spaces/`, and `L²` is taken over
`[0,∞) × [0,π/2]` with the measure `dz dθ` (the paper's Warning in §Notation:
**not** `z dz dθ`).  The radial variable of `L₁₂` is called `z` here (the paper
switches to `ρ`/`R` inside the integral; see `Work.FM.L12`).

## The operators

* `L f = f + z ∂_z f - 2 f/(1+z)`                                    (`𝓛`)
* `LGamma α f = L f - (2 z Γ(θ)/(c (1+z)²)) L₁₂(f)`                  (`𝓛_Γ`)
* `Proj α f = f - (Γ(θ)/c)(2 z²/(1+z)³) L₁₂(f)(0)`                    (`𝕡`)
* `Transport f = 3 sin(2θ) ∂_θ f/(1+z)`
* `LGammaT α f = LGamma α f - Proj α (Transport f)`                   (`𝓛_Γ^T`)

## The inner products and energies

* `ip g₁ g₂ = ∫∫ g₁ g₂` (the `L²` inner product), `wip ρ g₁ g₂ = ∫∫ g₁ g₂ ρ`.
* `L2Sqz g = ∫_0^∞ g²` and `L2SqzW ρ g = ∫_0^∞ g² ρ` for *radial* functions
  (`L₁₂(f)` is radial: as an energy its `θ`-integral is a factor `π/2`, so the
  paper's `|z^{-1}L₁₂(f)|²_{L²_z}` is `L2Sqz (fun z => L12f f z / z)`).
* `Etheta1 α f`, `Eztheta1 α f` are the paper's `E_θ¹`, `E_{z,θ}¹`;
  `Eztheta1 α f = HkSq α 1 f` (`Eztheta1_eq_HkSq_one`).
* `H1IP α` is the paper's `ℋ¹` inner product; `IsHkIP α k IP` is the paper's
  specification of an admissible inner product on `ℋ^k` (properties (i),(ii) of
  §"Higher order derivatives and the inner product on `ℋ^k`"), and `HkIPStep`
  is the paper's inductive step
  `(f,g)_{ℋ^k} = (f,g)_{ℋ^{k-1}} + c_{1,k}(D_θf,D_θg)_{ℋ^{k-1}} + c_{2,k}(D_zf,D_zg)_{ℋ^{k-1}}`.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FM.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The linearized operators -/

/-- The paper's operator `L₁₂` applied to a function of `(z,θ)`; the result is a
function of the radial variable `z` alone.  With `Work.Spaces.K θ = 3 sin θ cos²θ`,
this is `L₁₂(f)(z) = ∫_z^∞ ∫_0^{π/2} K(θ') f(s,θ')/s dθ' ds`. -/
def L12f (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => FM.L12 Spaces.K f z

/-- `𝓛(f) = f + z ∂_z f - 2 f/(1+z)`. -/
def L (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ + Spaces.Dz f z θ - 2 * f z θ / (1 + z)

/-- `𝓛_Γ(f) = 𝓛(f) - (2 z Γ(θ)/(c(1+z)²)) L₁₂(f)`. -/
def LGamma (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => L f z θ - (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z

/-- `𝕡(f)(z,θ) = f(z,θ) - (Γ(θ)/c) (2 z²/(1+z)³) L₁₂(f)(0)`. -/
def Proj (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ - (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * L12f f 0

/-- The angular transport term `3 sin(2θ) ∂_θ f /(1+z) = 3 D_θ f/(1+z)`. -/
def Transport (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => 3 * Spaces.Dth f z θ / (1 + z)

/-- `𝓛_Γ^T(f) = 𝓛_Γ(f) - 𝕡(3 sin(2θ) ∂_θ f/(1+z))`. -/
def LGammaT (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => LGamma α f z θ - Proj α (Transport f) z θ

/-! ## Inner products, weights and energies -/

/-- The `L²` inner product over `[0,∞) × [0,π/2]` with measure `dz dθ`. -/
def ip (g₁ g₂ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, g₁ z θ * g₂ z θ

/-- The `ρ`-weighted `L²` inner product: `∫∫ g₁ g₂ ρ`. -/
def wip (ρ g₁ g₂ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, g₁ z θ * g₂ z θ * ρ z θ

/-- The weighted squared `L²` norm `∫∫ g² ρ`. -/
def L2SqW (ρ g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (g z θ) ^ 2 * ρ z θ

/-- The squared `L²` norm of a *radial* function, `∫_0^∞ g(z)² dz`. -/
def L2Sqz (g : ℝ → ℝ) : ℝ := ∫ z in Spaces.Iz, (g z) ^ 2

/-- The weighted squared `L²` norm of a radial function, `∫_0^∞ g(z)² ρ(z) dz`. -/
def L2SqzW (ρ : ℝ → ℝ) (g : ℝ → ℝ) : ℝ := ∫ z in Spaces.Iz, (g z) ^ 2 * ρ z

/-- The weight `w/√(sin(2θ)^γ)`; note `wtGam (gam α) = Spaces.Wt α`. -/
def wtGam (γ z θ : ℝ) : ℝ := Spaces.w z * (Real.sin (2 * θ)) ^ (-(γ / 2))

/-- The weight `w/√(sin(2θ)^η)` with the paper's `η = 99/100`. -/
def wtEta (z θ : ℝ) : ℝ := wtGam Spaces.eta z θ

/-- `|f w|²_{L²}`. -/
def Ef (f : ℝ → ℝ → ℝ) : ℝ := Spaces.L2Sq (fun z θ => f z θ * Spaces.w z)

/-- `|D_z f · w/√(sin(2θ)^η)|²_{L²}`. -/
def EDz (f : ℝ → ℝ → ℝ) : ℝ := Spaces.L2Sq (fun z θ => Spaces.Dz f z θ * wtEta z θ)

/-- `|D_θ f · w/√(sin(2θ)^γ)|²_{L²}`. -/
def EDth (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  Spaces.L2Sq (fun z θ => Spaces.Dth f z θ * wtGam (Spaces.gam α) z θ)

/-- `|f · w/√(sin(2θ)^η)|²_{L²}`. -/
def EfEta (f : ℝ → ℝ → ℝ) : ℝ := Spaces.L2Sq (fun z θ => f z θ * wtEta z θ)

/-- `|z^{-1} L₁₂(f)|²_{L²_z}` (radial `L²` norm, no angular factor). -/
def EL12z (f : ℝ → ℝ → ℝ) : ℝ := L2Sqz (fun z => L12f f z / z)

/-- `|D_θ f · w|²_{L²}` — the `L²` norm of the angular derivative with the *radial*
weight only (the error term of Proposition `L2CoercivityTransport`). -/
def EDthW (f : ℝ → ℝ → ℝ) : ℝ :=
  wip (fun z _ => Spaces.w z ^ 2) (Spaces.Dth f) (Spaces.Dth f)

/-- The paper's energy `E_θ¹ = |D_θ f w/√(sin(2θ)^γ)|² + |f w/√(sin(2θ)^η)|²`. -/
def Etheta1 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ := EDth α f + EfEta f

/-- The paper's energy
`E_{z,θ}¹ = |D_z f w/√(sin(2θ)^η)|² + |D_θ f w/√(sin(2θ)^γ)|² + |f w/√(sin(2θ)^η)|²`. -/
def Eztheta1 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ := EDz f + EDth α f + EfEta f

/-- The paper's inner product on `ℋ¹`:
`10(D_zf,D_zg w²/sin^η) + 10^10(fw,gw/sin^η) + 10^17(fw,gw) + 10^21(D_θf,D_θg w²/sin^γ)`. -/
def H1IP (α : ℝ) (f g : ℝ → ℝ → ℝ) : ℝ :=
  10 * wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) (Spaces.Dz f) (Spaces.Dz g)
    + (10 : ℝ) ^ 10 * wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) f g
    + (10 : ℝ) ^ 17 * wip (fun z _ => Spaces.w z ^ 2) f g
    + (10 : ℝ) ^ 21 * wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
        (Spaces.Dth f) (Spaces.Dth g)

/-- The paper's inductive step for the inner product on `ℋ^k`:
`(f,g)_{ℋ^k} = (f,g)_{ℋ^{k-1}} + c₁(D_θf,D_θg)_{ℋ^{k-1}} + c₂(D_zf,D_zg)_{ℋ^{k-1}}`. -/
def HkIPStep (c₁ c₂ : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ)
    (f g : ℝ → ℝ → ℝ) : ℝ :=
  IP f g + c₁ * IP (Spaces.Dth f) (Spaces.Dth g) + c₂ * IP (Spaces.Dz f) (Spaces.Dz g)

/-- The admissible class of the `ℋ^k` coercivity layer: `f` is smooth on a neighbourhood
of the closed quadrant, and **every** mixed `D`-derivative `D_z^b D_θ^a f` with `a + b ≤ k`
lies in `ℋ^k` and has vanishing `L₁₂`-zero-mode `L₁₂(D_z^bD_θ^a f)(0) = 0`.  The zero-mode
conditions are the paper's projector conditions ("if `g` vanishes quadratically at `z = 0`
and `L₁₂(g)(0) = 0` then the same can be said about `𝓛_Γ^T(g)`"); they are exactly what
makes the commutator defects `E₁`, `E₂` lie honestly in `ℋⁿ`.  The class is closed under
`D_θ` and `D_z` (`HkAdm_dth`), which is what the induction needs. -/
def HkAdm (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  Spaces.SmoothNbhd f ∧
    (∀ a b : ℕ, a + b ≤ k → Spaces.HkMem α k (Spaces.mixed b a f)) ∧
    (∀ a b : ℕ, a + b ≤ k → L12f (Spaces.mixed b a f) 0 = 0)

/-- `IP` is an admissible inner product on `ℋ^k` in the sense of the paper's
§"Higher order derivatives and the inner product on `ℋ^k`".  It is a **globally** additive
and homogeneous functional with nonnegative diagonal — the paper's induction writes
`IP (D_θ𝓛_Γ^T f) (D_θ f) = IP (𝓛_Γ^T(D_θ f)) (D_θ f) + IP E₁ (D_θ f)` and applies
Cauchy–Schwarz, both of which need linearity *unrestricted by membership* — while the
comparability with the `ℋ^k` norm and the coercivity of `𝓛_Γ^T` are required only on the
admissible class `HkAdm α k`.  (Restricting linearity as well makes the induction step
false: outside the `L₁₂`-zero-mode case the defect `E₁` is not in `ℋⁿ`, so no
membership-restricted clause applies to it.) -/
def IsHkIP (α : ℝ) (k : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) : Prop :=
  (∀ (f₁ f₂ g : ℝ → ℝ → ℝ), Spaces.SmoothNbhd f₁ → Spaces.SmoothNbhd f₂ →
    Spaces.SmoothNbhd g → Spaces.HkMem α k f₁ → Spaces.HkMem α k f₂ →
    Spaces.HkMem α k g → IP (f₁ + f₂) g = IP f₁ g + IP f₂ g) ∧
  (∀ (c : ℝ) (f g : ℝ → ℝ → ℝ), Spaces.SmoothNbhd f → Spaces.SmoothNbhd g →
    Spaces.HkMem α k f → Spaces.HkMem α k g →
    IP (fun z θ => c * f z θ) g = c * IP f g) ∧
  (∀ (h : ℝ → ℝ → ℝ), 0 ≤ IP h h) ∧
  (∀ f, HkAdm α k f → Spaces.HkSq α k f ≤ IP f f) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ f, HkAdm α k f → IP f f ≤ C * Spaces.HkSq α k f) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ f, HkAdm α k f → c * Spaces.HkSq α k f ≤ IP (LGammaT α f) f)

/-- The commutator defect `E₁` of `D_θ` and `𝓛_Γ^T`, in the `ℋ^n` norm:
`D_θ 𝓛_Γ^T f = 𝓛_Γ^T(D_θ f) + E₁` with `E₁ ∈ ℋⁿ` and `|E₁|_{ℋⁿ} ≤ C|f|_{ℋⁿ}`.  This is
the paper's estimate `|E₁|_{ℋ^{k-1}} ≤ C̄_k|f|_{ℋ^{k-1}}` which is the input to the
induction step constructing the inner product on `ℋ^k`.  Membership of `E₁` in `ℋⁿ` is
part of the conclusion: it is what lets the induction pair `E₁` with `D_θf`. -/
def CommutTheta (α : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Spaces.SmoothNbhd f → Spaces.HkMem α n f →
    Spaces.HkSq α n (fun z θ =>
        Spaces.Dth (LGammaT α f) z θ - LGammaT α (Spaces.Dth f) z θ)
      ≤ C * Spaces.HkSq α n f

/-- The commutator defect `E₂` of `D_z` and `𝓛_Γ^T`, in the `ℋ^n` norm:
`D_z 𝓛_Γ^T f = 𝓛_Γ^T(D_z f) + E₂` with `E₂ ∈ ℋⁿ` and
`|E₂|_{ℋⁿ} ≤ C(|f|_{ℋⁿ} + |D_θ f|_{ℋⁿ})`. -/
def CommutZ (α : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Spaces.SmoothNbhd f → Spaces.HkMem α n f →
    Spaces.HkMem α n (Spaces.Dth f) →
    Spaces.HkSq α n (fun z θ =>
        Spaces.Dz (LGammaT α f) z θ - LGammaT α (Spaces.Dz f) z θ)
      ≤ C * (Spaces.HkSq α n f + Spaces.HkSq α n (Spaces.Dth f))

/-- The paper's condition (GammaAssumption): `|Γ/c - K|_{L²([0,π/2])} ≤ 7/10`. -/
def GammaL2Bnd (α : ℝ) : Prop :=
  ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2 ≤ (7 / 10 : ℝ) ^ 2

/-- The paper's pointwise condition (GammaAssumption2):
`|sin(2θ) ∂_θΓ| ≤ 2αΓ` on the angular interval. -/
def GammaPointwiseBnd (α : ℝ) : Prop :=
  ∀ θ ∈ Spaces.Iθ, |Real.sin (2 * θ) * deriv (fun t => Spaces.Gam α t) θ| ≤ 2 * α * Spaces.Gam α θ


/-! ## The analytic hypothesis package for the integration by parts -/

/-- `u` is a function of the self-similar variables on which the `z`-integration by
parts of this chapter is valid.  This is the class of functions the paper works with:
for the Hardy lemma it says "We will establish the result for smooth functions with `f`
and `L₁₂(f)` vanishing (at least) quadratically at zero. The general case will follow by
approximation."  Concretely we require

* `u` is smooth on a neighbourhood of the closed quadrant (`Spaces.SmoothNbhd`), so that
  every `θ`-slice is differentiable on `(0,∞)` and every `z`-slice on `(0,π/2)`;
* the boundary term `z (u w)²` tends to `0` at `z = 0⁺` and at `z = ∞` (this is what
  makes the boundary term of the `z`-integration by parts vanish; it holds for every
  `u` vanishing to second order at `z = 0` and decaying at infinity);
* the weighted square `(u w)²` is integrable on each `θ`-slice and on the whole
  quadrant;
* the derivative `∂_z (z (u w)²)` is integrable on each `θ`-slice (the hypothesis needed
  by the fundamental theorem of calculus on `(0,∞)`).

The `θ`-integration by parts of §6 needs no extra boundary hypothesis: the boundary term
is `sin(2θ) u(z,θ)²`, which vanishes at both endpoints of `Iθ` for the functions used
there (`u = D_θ f` always carries a factor `sin(2θ)`). -/
structure IBP (u : ℝ → ℝ → ℝ) : Prop where
  /-- `u` is smooth on a neighbourhood of the closed quadrant. -/
  smooth : Spaces.SmoothNbhd u
  /-- the boundary term `z (u w)²` vanishes at `z = 0`. -/
  bd0 : ∀ θ ∈ Spaces.Iθ, Tendsto (fun z => z * (u z θ * Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0)
  /-- the boundary term `z (u w)²` vanishes at `z = ∞`. -/
  bdTop : ∀ θ ∈ Spaces.Iθ, Tendsto (fun z => z * (u z θ * Spaces.w z) ^ 2) atTop (𝓝 0)
  /-- the weighted square is integrable on each `θ`-slice. -/
  intSq : ∀ θ ∈ Spaces.Iθ, IntegrableOn (fun z => (u z θ * Spaces.w z) ^ 2) (Set.Ioi 0)
  /-- the weighted square is integrable on the quadrant. -/
  intSqProd : IntegrableOn (fun p : ℝ × ℝ => (u p.1 p.2 * Spaces.w p.1) ^ 2)
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the derivative of the boundary term is integrable on each `θ`-slice. -/
  intDeriv : ∀ θ ∈ Spaces.Iθ,
    IntegrableOn (fun z => deriv (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z) (Set.Ioi 0)
  /-- the integrand of `wip_L_self` is jointly integrable. -/
  intL : IntegrableOn (Function.uncurry (fun z θ => L u z θ * u z θ * Spaces.w z ^ 2))
    (Spaces.Iz ×ˢ Spaces.Iθ)

/-- The analytic hypotheses of the Hardy-weight lemma (`Lemma HardyWeight` of the paper):
`f` has integrable angular slices, the radial density `L₁₂(f)` is continuous and
integrable on `(0,∞)`, all the boundary terms `L₁₂(f)² · z^{1-2j}` (`j = 0,1,2`) and
`w · L₁₂(f)²` vanish at `0⁺` and at `∞`, and the integrals occurring in the proof
converge.  The paper assumes "`f w ∈ L²` and `L₁₂(f) w ∈ L²`", which is what forces
`L₁₂(f)(0) = 0` and hence the vanishing of the boundary terms. -/
structure HardyHyp (f : ℝ → ℝ → ℝ) : Prop where
  /-- the angular slices of `f` are integrable, so that `L12dens` is the honest density. -/
  hslice : ∀ z ∈ Set.Ioi 0, IntegrableOn (fun θ => Spaces.K θ * f z θ / z) Spaces.Iθ
  /-- `L12dens` is continuous on `(0,∞)` (for the fundamental theorem of calculus). -/
  hcont : ∀ z ∈ Set.Ioi 0, ContinuousAt (FM.L12dens Spaces.K f) z
  /-- the density is integrable on `(0,∞)`. -/
  hint : IntegrableOn (FM.L12dens Spaces.K f) (Set.Ioi 0)
  /-- the component integrals of `L₁₂(f)` converge. -/
  intA : ∀ j : ℕ, j ≤ 2 → IntegrableOn (fun z => (L12f f z) ^ 2 / z ^ (2 * (j : ℝ))) (Set.Ioi 0)
  /-- the comparison component integrals of `f` converge. -/
  intB : ∀ j : ℕ, j ≤ 2 →
    IntegrableOn (fun z => (∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ))) (Set.Ioi 0)
  /-- the boundary terms `L₁₂(f)² z^{1-2j}` vanish at `z = 0`. -/
  bd0 : ∀ j : ℕ, j ≤ 2 →
    Tendsto (fun z => (L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1)) (𝓝[>] 0) (𝓝 0)
    ∧ Tendsto (fun z => Spaces.w z * (L12f f z) ^ 2) (𝓝[>] 0) (𝓝 0)
  /-- the boundary terms `L₁₂(f)² z^{1-2j}` vanish at `z = ∞`. -/
  bdTop : ∀ j : ℕ, j ≤ 2 →
    Tendsto (fun z => (L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1)) atTop (𝓝 0)
    ∧ Tendsto (fun z => Spaces.w z * (L12f f z) ^ 2) atTop (𝓝 0)

/-- The joint-integrability data needed by the `L²` coercivity chain of §6: every product
of an ingredient of `𝓛_Γ^T` (or of its `D_θ`/`D_z` derivative) with `f` against the
square of the weight and the relevant angular weight is jointly integrable on the
quadrant.  Under these hypotheses every `wip` occurring in the paper's estimates is an
honest finite number rather than Lean's junk value for a non-integrable integrand. -/
structure CoerciveData (α : ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  /-- the `𝓛 f · f w²` product is integrable. -/
  intL : IntegrableOn (Function.uncurry (fun z θ => L f z θ * f z θ * Spaces.w z ^ 2))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `L₁₂`-term of `𝓛_Γ` against `f w²` is integrable. -/
  intL12 : IntegrableOn (Function.uncurry (fun z θ =>
    (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z * f z θ
      * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `𝓛_Γ f · f w²` product is integrable. -/
  intLG : IntegrableOn (Function.uncurry (fun z θ => LGamma α f z θ * f z θ * Spaces.w z ^ 2))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the transport term against `f w²` is integrable. -/
  intT : IntegrableOn (Function.uncurry (fun z θ => Transport f z θ * f z θ * Spaces.w z ^ 2))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the projector correction against `f w²` is integrable. -/
  intP : IntegrableOn (Function.uncurry (fun z θ =>
    Proj α (Transport f) z θ * f z θ * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `𝓛_Γ^T f · f w²` product is integrable. -/
  intLGT : IntegrableOn (Function.uncurry (fun z θ =>
    LGammaT α f z θ * f z θ * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `K`-part of the `L₁₂` integration by parts. -/
  intK : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ))) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `(Γ/c - K)`-part of the `L₁₂` integration by parts. -/
  intG : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.w z / z * L12f f z * ((Spaces.Gam α θ / Spaces.c α - Spaces.K θ) * f z θ)))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-η}`-weighted `𝓛_Γ^T f · f w²` product is integrable. -/
  intLGTeta : IntegrableOn (Function.uncurry (fun z θ =>
    LGammaT α f z θ * f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-η}`-weighted `f² w²` product is integrable. -/
  intFeta : IntegrableOn (Function.uncurry (fun z θ =>
    f z θ * f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `|D_θ f w|²` product is integrable. -/
  intDth : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.Dth f z θ * Spaces.Dth f z θ * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-γ}`-weighted `(D_θ f)² w²` product is integrable. -/
  intDthGam : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.Dth f z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
      * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-γ}`-weighted `D_θ𝓛_Γ^T f · D_θ f w²` product is integrable. -/
  intDthDth : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.Dth (LGammaT α f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
      * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-η}`-weighted `D_z𝓛_Γ^T f · D_z f w²` product is integrable. -/
  intDzDz : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.Dz (LGammaT α f) z θ * Spaces.Dz f z θ * Spaces.w z ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-η}`-weighted `(D_z f)² w²` product is integrable. -/
  intDz : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.Dz f z θ * Spaces.Dz f z θ * Spaces.w z ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ)

/-! ## Elementary API -/

theorem Wt_eq_wtGam (α : ℝ) (z θ : ℝ) :
    Spaces.Wt α z θ = wtGam (Spaces.gam α) z θ := rfl

theorem L2Sq_eq_ip (g : ℝ → ℝ → ℝ) : Spaces.L2Sq g = ip g g := by
  simp only [Spaces.L2Sq, ip, pow_two]

theorem L2SqW_eq_wip (ρ g : ℝ → ℝ → ℝ) : L2SqW ρ g = wip ρ g g := by
  simp only [L2SqW, wip, pow_two]

/-- The weights are positive on the *open* quadrant.  (At `θ = 0` and `θ = π/2`
Lean's totalised `rpow` gives the value `0`, which is harmless: `{0, π/2}` is a null
set and the weight is only ever integrated.  This is the same convention as
`Work.Spaces.Wt`; see `Wt_eq_wtGam`.) -/
theorem wtGam_pos {γ z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < wtGam γ z θ := by
  rw [wtGam]
  have h1 : 0 < Spaces.w z := by
    rw [Spaces.w]; positivity
  have h2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  exact mul_pos h1 (Real.rpow_pos_of_pos h2 _)

theorem Ef_eq (f : ℝ → ℝ → ℝ) : Ef f = Spaces.L2Sq (fun z θ => f z θ * Spaces.w z) := rfl

theorem eta_eq : Spaces.eta = 99 / 100 := rfl

theorem gam_eq (α : ℝ) : Spaces.gam α = 1 + α / 10 := rfl

theorem Etheta1_eq (α : ℝ) (f : ℝ → ℝ → ℝ) : Etheta1 α f = EDth α f + EfEta f := rfl

theorem Eztheta1_eq (α : ℝ) (f : ℝ → ℝ → ℝ) : Eztheta1 α f = EDz f + EDth α f + EfEta f := rfl

theorem LGamma_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    LGamma α f z θ
      = L f z θ - (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z := rfl

theorem LGammaT_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    LGammaT α f z θ
      = LGamma α f z θ - Proj α (Transport f) z θ := rfl

theorem Proj_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Proj α f z θ
      = f z θ - (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * L12f f 0 := rfl

theorem Transport_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Transport f z θ = 3 * Spaces.Dth f z θ / (1 + z) := rfl

end Work.Coercivity
