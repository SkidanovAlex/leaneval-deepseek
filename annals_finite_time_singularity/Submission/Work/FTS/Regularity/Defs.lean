/-
# `Work.FTS.Regularity.Defs` — the `RegPkg` interface of node N7

This is the area of the `fts` / `annals_finite_time_singularity` project that owns **node N7** of
the lead's audit (`FTS_AUDIT_LEAD.md` §4):

> N7. Regularity transfer (20--40K).
> * Weighted `𝓗⁴`/`𝓦^{l,∞}` bounds in `(z,θ)` imply that the physical `ω(·,t)` is `C^β`
>   (`β = α_paper/3`, i.e. the challenge `α`) and compactly supported, uniformly on `[0,S]`.
> * This includes behaviour on the `x₃`-axis and the plane `x₃=0`, where the data are only Hölder.
> * Use the `Γ`-structure and the `WtoH`/`W^{5,∞}` facts.

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
  Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887.

The route of the audit replaces the (vacuous) delivered interface by a *dynamically rescaled*
construction: the paper's fake-time equation, evaluated at the modulation `(μ(τ), λ(τ))` recomputed
at each `τ`, **is** the dynamically rescaled Euler equation, and the global a-priori bound of §
"Final a-priori estimate on `g`" gives blow-up directly.  The output of that existence theorem
(node N6) is a *regularity package* for the self-similar profile:

* the perturbation `g = F - F_*` of the profile `F_* = α(Γ/c)·2z/(1+z)²` of the paper, as a
  family `g(·,·,τ)` in fake time;
* a **clock** `(A,B)`: the physical vorticity of the reconstruction is
  `ω(x,τ) = A(τ)⁻¹·F(ρ(x)^{3α}/B(τ), θ(x), τ)·e_θ(x)`;
* the *quantitative* data of the profile: the angular vanishing `|g| ≤ Cv·Γ(θ)` (the paper's
  `St1`-class datum), the joint `α`-Hölder moduli in `(z,θ,τ)`, the quadratic vanishing at
  `z = 0`, the compact support of the full profile `F = F_* + g`, the honest `ℋ⁴`-membership,
  and the first-order-in-`τ` data (the `τ`-derivative of `g` with its bounds).

This module sets up the vocabulary: `JointHolder` (the joint `α`-Hölder data in the self-similar
variables), the structure `RegPkg` (the interface), and the physical fields `physVort` (the
vorticity `ω`), `physVel` (the velocity `u = BS ω`) and their slices.  The *transfer theorems* —
that `RegPkg` makes `ω` jointly `α`-Hölder and compactly supported, and `u` jointly `C^{1,α}` —
are in the sibling modules `Slice`, `Time`, `Bundle` and `Transfer`.

## Conventions

* The self-similar variables are curried, `f : ℝ → ℝ → ℝ`, applied as `f z θ`; the domain is
  `Iz ×ˢ Iθ = [0,∞) × [0,π/2]`, with the measure `dz dθ` (**not** `z dz dθ`) — the convention of
  `Work.Spaces`.
* `ρ(x) = ‖x‖` is `Work.Cyl.rho`, `θ(x) = arctan(x₃/r)` is `Work.Cyl.theta`, and `e_θ` is
  `Work.Cyl.eTheta` (junk `0` on the axis, which is the right value there).
* The **profile exponent** is `3α`, where `α` is the challenge's Hölder exponent: the paper's
  `Γ = (sinθcos²θ)^{α_paper/3}` equals `(sinθcos²θ)^α` with `α = α_paper/3`
  (`Work.ConstructionInstance.profExp`), so the physical vorticity vanishes like `θ^α` on the
  plane and like `(r/ρ)^{2α}` on the axis.  This is what makes the `e_θ`-field `α`-Hölder (and the
  velocity `C^{1,α}`) — the audit's "`β = α_paper/3`".
* `F_* = Work.Construction.Fstar (3α)` is the paper's full profile at the localized scale, and the
  perturbation is `g = F - F_*`, so that the physical vorticity is
  `Work.ConstructionInstance.omegaS` of `g` (Definitionally: `profile (3α) g z θ = F_* z θ + g z θ`
  for `θ ≥ 0`, with the odd extension for `θ < 0`).

## Inhabitation

The lead's rule "every interface structure must come with an inhabitation obligation" is honoured
in `Inhabited.lean`: for every `0 < α ≤ 1/3` there are explicit `A, B, g` with `RegPkg α 1 A B g`
— the localized static profile `g = -F_*·(1 - χ(z/L))` with the constant clock — so the interface
is not vacuous.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.Construction.Defs
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.Stability.Cutoff
import Submission.Work.CoreResiduals.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Regularity

/-- `ℝ³`, definitionally `Work.Cyl.R3`, `Work.LWP.R3`, `Work.CoreResiduals.R3` and
`Work.FTS.Physical.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The profile exponent and the angular factor -/

/-- The **profile exponent** `p = 3α` of the route (the paper's `α_paper`), so that the paper's
`Γ = (sinθcos²θ)^{α_paper/3}` is `(sinθcos²θ)^α`. -/
def pExp (α : ℝ) : ℝ := 3 * α

@[simp] theorem pExp_eq (α : ℝ) : pExp α = 3 * α := rfl

theorem pExp_pos {α : ℝ} (hα : 0 < α) : 0 < pExp α := by rw [pExp]; linarith

theorem pExp_le_one {α : ℝ} (hα13 : α ≤ 1 / 3) : pExp α ≤ 1 := by rw [pExp]; linarith

theorem pExp_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ pExp α := (pExp_pos hα).le

/-! ## The explicit Hölder constants of the per-slice transfer

The two constants below are the ones produced by the *existing* proofs of the two quantitative
inputs of the per-slice transfer (`Work.ConstructionInstance.holder_gComp` and
`Work.ConstructionInstance.holder_smul_eTheta`).  They are exposed here as *named* reals so that
the transfer lemmas of this chapter can be stated with an explicit constant — which is what makes
them uniform in the time parameter `τ` (an existential constant produced inside a `∀ τ` cannot be
used uniformly, see the module docstring of `Slice.lean`). -/

/-- The explicit Hölder constant of the composite profile
`x ↦ g (ρ(x)^{3α}) (|θ(x)|)` proved in `Work.ConstructionInstance.holder_gComp`: it is that
proof's `C` in terms of the data constants `Cv` (angular vanishing), `Lg` (radial modulus),
`Lθ` (angular modulus) and `K` (the `z = 0` Taylor/Lipschitz datum). -/
def gCompConst (α Cv Lg Lθ K : ℝ) : ℝ :=
  2 * Cv + (2 * Cv * (3 / 2) ^ α
    + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3 / 2) * 3 ^ α * (3 / 2) ^ (2 * α)
        + K * (3 / 2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))))

/-- `gCompConst` as a nonnegative real. -/
def gCompConstNN (α Cv Lg Lθ K : ℝ) : ℝ≥0 :=
  ⟨|gCompConst α Cv Lg Lθ K|, abs_nonneg _⟩

/-- The explicit Hölder constant of `x ↦ A x • e_θ(x)` proved in
`Work.ConstructionInstance.holder_smul_eTheta`: it is `CA + 2·Ca`, the Hölder constant of the
amplitude plus twice its vanishing rate. -/
def smulEThetaConst (CA Ca : ℝ) : ℝ≥0 := ⟨|CA + 2 * Ca|, abs_nonneg _⟩

/-- The angular factor `Γ(θ) = (sinθcos²θ)^α` of the route (this is `Work.ConstructionInstance.Gamma`
at the challenge's exponent `α`; the paper's `Γ` at `α_paper = 3α` is the same function). -/
abbrev Gamma (α θ : ℝ) : ℝ := Work.ConstructionInstance.Gamma α θ

theorem Gamma_eq_Gam (α θ : ℝ) : Gamma α θ = Work.Spaces.Gam (pExp α) θ := by
  simp only [Gamma, Work.ConstructionInstance.Gamma, Work.Spaces.Gam, pExp]
  norm_num

/-! ## The full profile and the perturbation -/

/-- The **full self-similar profile** `F(z,θ,τ) = F_*(z,θ) + g(z,θ,τ)`: the paper's profile
`F_*` plus the modulation `g`.  The physical vorticity is this profile composed with the
self-similar variables. -/
def profFull (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) : ℝ :=
  Work.Construction.Fstar (pExp α) z θ + g z θ τ

@[simp] theorem profFull_apply (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) :
    profFull α g z θ τ = Work.Construction.Fstar (pExp α) z θ + g z θ τ := rfl

/-- The `τ`-slice of the perturbation, as a two-variable profile. -/
def gSlice (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) : ℝ → ℝ → ℝ := fun z θ => g z θ τ

@[simp] theorem gSlice_apply (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ) :
    gSlice g τ z θ = g z θ τ := rfl

/-- The `τ`-slice of the full profile. -/
def profSlice (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => profFull α g z θ τ

@[simp] theorem profSlice_apply (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ) :
    profSlice α g τ z θ = profFull α g z θ τ := rfl

/-! ## The joint `α`-Hölder data in the self-similar variables -/

/-- **The joint `α`-Hölder class of the self-similar variables.**  `h : ℝ → ℝ → ℝ → ℝ` is
`α`-Hölder for the metric `|Δz| + |Δθ| + |Δτ|` on the domain `z ≥ 0`, `θ ∈ [0,π/2]`, with
constant `N` (`N ≥ 0`).

This is the form in which the route's `𝓗⁴`/`𝓦^{l,∞}` bounds on the profile enter the physical
transfer: the `(z,θ)` part at fixed `τ` gives the two moduli `hzk`/`hzth` of the `St1`-class data
(`Work.ConstructionInstance.holder_gComp`), the `τ` part gives the time-Hölder continuity of the
physical field, and the *joint* form is what makes the composition with `(x,τ) ↦ (z(x,τ),θ(x),τ)`
`α`-Hölder without any separate uniformity argument. -/
def JointHolder (α N : ℝ) (h : ℝ → ℝ → ℝ → ℝ) : Prop :=
  0 ≤ N ∧ ∀ z z' θ θ' τ τ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
    |h z θ τ - h z' θ' τ'| ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α

/-- **The regularity jet of a self-similar profile on the strip `[0,S]`**: the family
`h : ℝ → ℝ → ℝ → ℝ` is both *bounded* by `N` on the domain `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]` **and**
jointly `α`-Hölder there for the metric `|Δz| + |Δθ| + |Δτ|` with the same constant `N`.

The two conjuncts are deliberately bundled with one constant: this is the "`𝓦^{l,∞}` box" form of
the paper's data (a bounded profile with a Hölder modulus), and it is the form in which the
`τ`-regularity of the physical field is transferred — every factor of the chain-rule formula for
`∂_τω` is then *both* bounded and `α`-Hölder, so no separate boundedness hypothesis is needed. -/
def Jet (α S N : ℝ) (h : ℝ → ℝ → ℝ → ℝ) : Prop :=
  0 ≤ N ∧ (∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → |h z θ τ| ≤ N) ∧
    ∀ z z' θ θ' τ τ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      τ ∈ Set.Icc 0 S → τ' ∈ Set.Icc 0 S →
        |h z θ τ - h z' θ' τ'| ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α

theorem Jet.nonneg {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h) : 0 ≤ N := H.1

/-- The uniform bound of a `Jet` at a strip time. -/
theorem Jet.abs_le {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h)
    {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |h z θ τ| ≤ N := H.2.1 z θ τ hz hθ hτ

/-- The `z`-modulus of a `Jet` at a fixed angle and time. -/
theorem Jet.zmod {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h)
    {z z' θ τ : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) :
    |h z θ τ - h z' θ τ| ≤ N * |z - z'| ^ α := by
  have h1 := H.2.2 z z' θ θ τ τ hz hz' hθ hθ hτ hτ
  simpa using h1

/-- The `θ`-modulus of a `Jet` at a fixed time. -/
theorem Jet.thmod {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h)
    {z θ θ' τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) :
    |h z θ τ - h z θ' τ| ≤ N * |θ - θ'| ^ α := by
  have h1 := H.2.2 z z θ θ' τ τ hz hz hθ hθ' hτ hτ
  simpa using h1

/-- The `τ`-modulus of a `Jet` at a fixed point of the domain. -/
theorem Jet.tmod {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h)
    {z θ τ τ' : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |h z θ τ - h z θ τ'| ≤ N * |τ - τ'| ^ α := by
  have h1 := H.2.2 z z θ θ τ τ' hz hz hθ hθ hτ hτ'
  simpa using h1

theorem JointHolder.nonneg {α N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : JointHolder α N h) : 0 ≤ N :=
  H.1

/-- The `(z,θ)`-modulus of a joint Hölder family at fixed `τ`. -/
theorem JointHolder.zmod {α N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : JointHolder α N h)
    {z z' θ τ : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (hθ : θ ∈ Work.Spaces.Iθ) :
    |h z θ τ - h z' θ τ| ≤ N * |z - z'| ^ α := by
  have h1 := H.2 z z' θ θ τ τ hz hz' hθ hθ
  simpa using h1

/-- The `θ`-modulus of a joint Hölder family at fixed `τ`. -/
theorem JointHolder.thmod {α N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : JointHolder α N h)
    {z θ θ' τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |h z θ τ - h z θ' τ| ≤ N * |θ - θ'| ^ α := by
  have h1 := H.2 z z θ θ' τ τ hz hz hθ hθ'
  simpa using h1

/-- The `τ`-modulus of a joint Hölder family at fixed `(z,θ)`. -/
theorem JointHolder.tmod {α N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : JointHolder α N h)
    {z θ τ τ' : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |h z θ τ - h z θ τ'| ≤ N * |τ - τ'| ^ α := by
  have h1 := H.2 z z θ θ τ τ' hz hz hθ hθ
  simpa using h1

/-! ## The interface `RegPkg` -/

/-- **THE REGULARITY PACKAGE `RegPkg`** of node N7: the quantitative data of the self-similar
profile (in fake time `τ ∈ [0,S]`) from which the physical regularity of the reconstructed
vorticity and velocity is transferred.

The parameters are the challenge's Hölder exponent `α`, the end `S` of the fake-time strip, the
two clock functions `A, B` (`ω = A(τ)⁻¹·F(ρ^{3α}/B(τ),θ,τ)·e_θ`) and the perturbation
`g = F - F_*`.

The fields are, in order:

* `hα`, `hα13`, `hS`: `0 < α ≤ 1/3` (the paper's regime) and `S > 0`;
* the **clock data**: positivity and two-sided bounds on the strip, differentiability with a
  bounded derivative, and an `α`-Hölder derivative (for the time-Hölder of `∂_τω`);
* the **structural profile data**: vanishing on the angular boundaries `θ = 0, π/2` and at
  `z = 0` (with `∂_z g(0,·) = 0`);
* the **joint `α`-Hölder data** of `g`, of `∂_z g` and of `∂_τ g` in `(z,θ,τ)` (`JointHolder`);
* the **angular vanishing** `|g| ≤ Cv·Γ(θ)` (the `St1`-class datum: it is what makes the physical
  `e_θ`-field vanish fast enough at the axis to be Hölder there);
* the **quadratic vanishing** `|g| ≤ K z²` for `z ≤ 2` (the Taylor datum at `z = 0`: it is what
  makes `|ĝ x| ≤ Ca·r(x)^α`, compensating the `1/r` singularity of `e_θ` at the axis);
* the **compact support** of the full profile `F = F_* + g`;
* the honest **`ℋ⁴`-membership** of each slice (the weighted space of the paper; membership makes
  `HkNorm (3α) 4` the sum of `L²`-norms of the weighted derivatives rather than a junk value);
* the **first-order `τ` data**: the joint `C¹` smoothness of `(z,τ) ↦ g z θ τ` at each fixed `θ`,
  which is what makes `τ ↦ ω(x,τ)` differentiable.

Every field is a statement about the *profile*, never about the physical fields: the transfer
theorems of the sibling modules prove the physical consequences. -/
structure RegPkg (α : ℝ) (S : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop where
  /-- `0 < α` (the Hölder exponent of the challenge) -/
  hα : 0 < α
  /-- the paper's regime `α ≤ 1/3` -/
  hα13 : α ≤ 1 / 3
  /-- the fake-time strip is nonempty -/
  hS : 0 < S
  /-- the amplitude of the physical vorticity is positive on the strip -/
  hA : ∀ τ ∈ Set.Icc 0 S, 0 < A τ
  /-- the self-similar scaling is positive on the strip -/
  hB : ∀ τ ∈ Set.Icc 0 S, 0 < B τ
  /-- the amplitude is bounded above and below on the strip -/
  hAb : ∃ a₀ a₁ : ℝ, 0 < a₀ ∧ ∀ τ ∈ Set.Icc 0 S, a₀ ≤ A τ ∧ A τ ≤ a₁
  /-- the scaling is bounded above and below on the strip -/
  hBb : ∃ b₀ b₁ : ℝ, 0 < b₀ ∧ ∀ τ ∈ Set.Icc 0 S, b₀ ≤ B τ ∧ B τ ≤ b₁
  /-- the amplitude is differentiable on the strip, with its `deriv` as derivative -/
  hAdiff : ∀ τ ∈ Set.Icc 0 S, HasDerivAt A (deriv A τ) τ
  /-- the scaling is differentiable on the strip, with its `deriv` as derivative -/
  hBdiff : ∀ τ ∈ Set.Icc 0 S, HasDerivAt B (deriv B τ) τ
  /-- the derivative of the amplitude is bounded on the strip -/
  hAd : ∃ a₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv A τ| ≤ a₂
  /-- the derivative of the scaling is bounded on the strip -/
  hBd : ∃ b₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv B τ| ≤ b₂
  /-- the derivative of the amplitude is `α`-Hölder on the strip -/
  hAdh : ∃ a₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |deriv A τ - deriv A τ'| ≤ a₃ * |τ - τ'| ^ α
  /-- the derivative of the scaling is `α`-Hölder on the strip -/
  hBdh : ∃ b₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |deriv B τ - deriv B τ'| ≤ b₃ * |τ - τ'| ^ α
  /-- the perturbation vanishes on the two angular boundaries -/
  hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (gSlice g τ)
  /-- the perturbation vanishes at `z = 0` -/
  hquad0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, g 0 θ τ = 0
  /-- `∂_z g` vanishes at `z = 0` -/
  hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.pz (gSlice g τ) 0 θ = 0
  /-- the joint `α`-Hölder data of the perturbation -/
  hg : ∃ Ng : ℝ, Jet α S Ng g
  /-- the joint `α`-Hölder data of `∂_z g` -/
  hpz : ∃ Npz : ℝ, Jet α S Npz (fun z θ τ => Work.Spaces.pz (gSlice g τ) z θ)
  /-- the joint `α`-Hölder data of `∂_τ g` -/
  hgdoth : ∃ Nd : ℝ, Jet α S Nd (fun z θ τ => deriv (fun s => g z θ s) τ)
  /-- the uniform angular vanishing `|g| ≤ Cv·Γ(θ)` of the perturbation -/
  hvan : ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
    |g z θ τ| ≤ Cv * Gamma α θ
  /-- the quadratic vanishing of `g` at `z = 0`, with the near-origin `z`- and `θ`-Lipschitz
  bounds of the slice: this is the Taylor datum of the paper's `St1`-class, and it is what makes
  `|ĝ x| ≤ Ca·r(x)^α` (`Work.ConstructionInstance.gComp_abs_le`), compensating the `1/r`
  singularity of `e_θ` at the axis -/
  htay : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
    (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
      |g z θ τ - g z' θ τ| ≤ K * max z z' * |z - z'|) ∧
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
      |g z θ τ - g z θ' τ| ≤ K * z * |θ - θ'|)
  /-- the full profile is compactly supported in the self-similar variable `z` -/
  hsupp : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z → profFull α g z θ τ = 0
  /-- the honest `ℋ⁴`-membership of every slice -/
  hH4 : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.HkMem (pExp α) 4 (gSlice g τ)
  /-- the joint `C¹` smoothness of `(z,τ) ↦ g z θ τ` at every fixed angle `θ ∈ Iθ` -/
  hcont : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1
    (fun q : ℝ × ℝ => g q.1 θ q.2) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1))

namespace RegPkg

variable {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}

theorem alpha_pos (h : RegPkg α S A B g) : 0 < α := h.hα
theorem alpha_le (h : RegPkg α S A B g) : α ≤ 1 / 3 := h.hα13
theorem strip_pos (h : RegPkg α S A B g) : 0 < S := h.hS

theorem pExp_pos (h : RegPkg α S A B g) : 0 < pExp α :=
  Work.FTS.Regularity.pExp_pos h.hα
theorem pExp_le_one (h : RegPkg α S A B g) : pExp α ≤ 1 :=
  Work.FTS.Regularity.pExp_le_one h.hα13

/-- The `VanishTheta` data, as a `Prop` about the slice. -/
theorem vanish (h : RegPkg α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Work.Spaces.VanishTheta (gSlice g τ) := h.hvt τ hτ

/-- The perturbation vanishes at `z = 0`. -/
theorem zero_z (h : RegPkg α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : g 0 θ τ = 0 := h.hquad0 τ hτ θ hθ

/-- The `z`-derivative of the perturbation vanishes at `z = 0`. -/
theorem zero_z_pz (h : RegPkg α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.pz (gSlice g τ) 0 θ = 0 :=
  h.hquad τ hτ θ hθ

/-- **Pointwise boundedness of the perturbation**: `|g| ≤ Cv` on the domain, since `Γ ≤ 1`. -/
theorem abs_le_Cv (h : RegPkg α S A B g) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv := by
  obtain ⟨Cv, hCv0, hCv⟩ := h.hvan
  refine ⟨Cv, hCv0, fun τ hτ z θ hz hθ => ?_⟩
  refine le_trans (hCv τ hτ z θ hz hθ) ?_
  have hθ' : θ ∈ Work.Spaces.Iθ := hθ
  have hΓ1 : Gamma α θ ≤ 1 := Work.ConstructionInstance.Gamma_le_one h.hα.le hθ
  have hΓ0 : 0 ≤ Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  nlinarith

/-- **The linear vanishing at `z = 0`**: `|g z θ τ| ≤ K z` for `z ∈ [0,1]`, which is the form of
the Taylor datum consumed by `Work.ConstructionInstance.gComp_abs_le`. -/
theorem abs_le_Kz (h : RegPkg α S A B g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → z ≤ 1 →
      θ ∈ Work.Spaces.Iθ → |g z θ τ| ≤ K * z := by
  obtain ⟨K, hK0, hK⟩ := h.htay
  refine ⟨K, hK0, fun τ hτ z θ hz hz1 hθ => ?_⟩
  have h1 := (hK τ hτ θ hθ).1 z hz (by linarith)
  have hz2 : z ^ 2 ≤ z := by nlinarith
  calc |g z θ τ| ≤ K * z ^ 2 := h1
    _ ≤ K * z := mul_le_mul_of_nonneg_left hz2 hK0

/-- **The boundedness box of the perturbation** from the regularity jet. -/
theorem abs_le_Ng (h : RegPkg α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ N := by
  obtain ⟨N, hN⟩ := h.hg
  exact ⟨N, hN.1, fun τ hτ z θ hz hθ => hN.abs_le hz hθ hτ⟩

/-- The uniform bound on `∂_z g` from the regularity jet. -/
theorem abs_le_Npz (h : RegPkg α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (gSlice g τ) z θ| ≤ N := by
  obtain ⟨N, hN⟩ := h.hpz
  exact ⟨N, hN.1, fun τ hτ z θ hz hθ => hN.abs_le hz hθ hτ⟩

/-- The uniform bound on `∂_τ g` from the regularity jet. -/
theorem abs_le_Nd (h : RegPkg α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |deriv (fun s => g z θ s) τ| ≤ N := by
  obtain ⟨N, hN⟩ := h.hgdoth
  exact ⟨N, hN.1, fun τ hτ z θ hz hθ => hN.abs_le hz hθ hτ⟩

/-- **The radial modulus of the perturbation at a strip time** (`Lg` of the `St1`-class). -/
theorem zmod (h : RegPkg α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ∃ Lg : ℝ, 0 ≤ Lg ∧ ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ τ - g z' θ τ| ≤ Lg * |z - z'| ^ α := by
  obtain ⟨N, hN⟩ := h.hg
  exact ⟨N, hN.1, fun z z' θ hz hz' hθ => hN.zmod hz hz' hθ hτ⟩

/-- **The angular modulus of the perturbation at a strip time** (`Lθ` of the `St1`-class). -/
theorem thmod (h : RegPkg α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ τ - g z θ' τ| ≤ Lθ * |θ - θ'| ^ α := by
  obtain ⟨N, hN⟩ := h.hg
  exact ⟨N, hN.1, fun z θ θ' hz hθ hθ' => hN.thmod hz hθ hθ' hτ⟩

/-- The Taylor data of the `St1`-class at a strip time, in the exact shape consumed by the
quantitative per-slice transfer. -/
theorem tay (h : RegPkg α S A B g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K * z * |θ - θ'|) := h.htay

end RegPkg

/-! ## The physical vorticity and velocity -/

/-- **THE PHYSICAL VORTICITY OF A SELF-SIMILAR PROFILE**, in physical time `τ`:

  `physVort α A B g x τ = A(τ)⁻¹ · F(ρ(x)^{3α}/B(τ), θ(x), τ) · e_θ(x)`,

where `F = F_* + g` is the full profile (`profFull`), `ρ(x) = ‖x‖`, `θ(x) = arctan(x₃/r)` and
`e_θ` is the azimuthal unit vector.  Equivalently (and definitionally, up to the odd extension of
the profile in `θ`), `physVort α A B g · τ = A(τ)⁻¹ • omegaSz (3α) (g · · τ) (ρ^{3α}/B(τ))`.

This is the paper's `ω^θ` as an `e_θ`-field: on the symmetry axis `r = 0` both `e_θ` (Lean's
junk `1/0 = 0`) and the `Γ`-factor of the profile vanish, so the field is `0` there — the value
that makes it continuous. -/
noncomputable def physVort (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : R3 → ℝ → R3 :=
  fun x τ => (A τ)⁻¹ • Work.ConstructionInstance.omegaSz (pExp α) (gSlice g τ)
    (Work.Cyl.rho x ^ pExp α / B τ) x

theorem physVort_apply (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) :
    physVort α A B g x τ = (A τ)⁻¹ • Work.ConstructionInstance.omegaSz (pExp α) (gSlice g τ)
      (Work.Cyl.rho x ^ pExp α / B τ) x := rfl

/-- The `τ`-slice of the physical vorticity is the unit-amplitude self-similar field of the
profile at the *rescaled* self-similar variable. -/
theorem physVort_slice (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) (x : R3) :
    physVort α A B g x τ = (A τ)⁻¹ •
      Work.ConstructionInstance.omegaSz (pExp α) (gSlice g τ)
        (Work.Cyl.rho x ^ pExp α / B τ) x := rfl

/-- **THE PHYSICAL VELOCITY**: the Biot–Savart field of the physical vorticity,
`physVel α A B g x τ = BS (physVort α A B g · τ) x`.  This is the object of node N8's
reconstruction and the target of the transfer theorem: `RegPkg` makes it jointly `C^{1,α}` on
`ℝ³ × [0,S]`.

The definition is the same as `Work.FTS.Physical.physVel (physVort α A B g)`; the two are
propositionally equal (`physVel_eq_Physical`). -/
noncomputable def physVel (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : R3 → ℝ → R3 :=
  fun x τ => Work.LWP.biotSavart (fun y => physVort α A B g y τ) x

theorem physVel_apply (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) :
    physVel α A B g x τ = Work.LWP.biotSavart (fun y => physVort α A B g y τ) x := rfl

theorem physVel_slice (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) :
    (physVel α A B g · τ) = Work.LWP.biotSavart (fun y => physVort α A B g y τ) := rfl

/-- The physical time derivative of the vorticity is the `deriv` of the slice. -/
theorem physVort_timeDeriv (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) :
    FiniteTimeSingularity.timeDeriv (physVort α A B g) x τ
      = deriv (fun s => physVort α A B g x s) τ := rfl

end Work.FTS.Regularity
