/-
# The GALERKIN area of the Elgindi finite-time-singularity project (audit node N6)

This directory (`Submission/Work/FTS/Galerkin/`, namespace `Work.FTS.Galerkin`) is the *skeleton*
of node **N6** of `FTS_AUDIT_LEAD.md` §4: *existence for the dynamic modulated equation by
Galerkin approximation plus compactness in the weighted `𝓗⁴`*.

The mathematical object is the paper's "fake time" evolution equation
(`Papers/elgindi/Classical_Euler_arXiv_2.tex`, tex 1559, `\eqref{gequationtime}`)

  `∂_τ g + 𝓛_Γ^T(g) = -μ̄(τ)(Γ/c)2z²/(1+z)³ + N₀ + N + N_* ,   g(z,θ,0) = g₀(z,θ)`,

with the **`τ`-dependent** modulation constant `μ̄(τ) = L₁₂(N₀)(0,τ) + L₁₂(N)(0,τ)` and
`λ(τ) = -2μ̄(τ)/(1+μ̄(τ))`; `IsDynEqOn`/`IsDynEq` below are exactly this equation, and
`muDyn` is the **sign-corrected** modulation constant `Construction.mufunS` (the sign fix of
`Submission/Work/FTS/FTS_MUFUN_SIGN.md` §5, option (a'): the transport zero-mode enters with a
`+`, so that `2α·muDyn = μ̄ + L₁₂(Transport g)(0)` and `(E)` needs no `L₁₂`-zero-mode hypothesis).
The paper-display constant `Construction.mufun` is retained but superseded.

All the operators (`𝓛_Γ^T` = `Work.Coercivity.LGammaT`, `N₀` = `N0`,
`N` = `N`, `N_*` = `Nstar`, `gRHS`, `lamfun`) are the existing vocabulary of
`Submission/Work/Construction/`; nothing is redefined here.

## What this file fixes

* **The equation** — `muDyn`, `lamDyn`, `dynLin`, `dynRHS`, `IsDynEqOn` (the honest half-line
  formulation `τ ≥ 0`, with the *within*-derivative on `Set.Ici 0`), `IsDynEq` (the two-sided
  form used by the audit's statement; it implies `IsDynEqOn`, and the converse holds for
  `τ > 0`), and the packaged solution predicates `IsDynGSolWith` / `IsDynGSol` / `IsDynGSolOn`.
* **The elliptic (stream-function) law** `EllLaw`, kept as an *explicit parameter* `Law` of the
  packaged predicates so that the sign convention of `Work.Elliptic.bslOp` (which is pinned by N1,
  see audit §4 N1) is not frozen here: pass `EllLaw α` for the `bslOp α Φ = F` convention (which
  is `Construction.StatEqPhi` on the open quadrant).
* **The regularity package** `RegPkg` (consumed by N7/N8); its `smooth` field is stated in the
  interior `C^∞` class `Work.Stability.smoothOrder`, not in the analytic order `⊤` (interface fix of
  2026-10-03).
* **The `ℋ⁴` inner-product interface** `IsH4Inner`: `Construction.IsH4IP` together with the
  *symmetry* of `IP`.  It is *kept* for the formal layer (`Hilbert.lean`, `Projection.lean`,
  `GalerkinODE.lean`), but it is **no longer the interface of the a-priori bundle**: it is not
  inhabited by the paper's inner product (Cauchy–Schwarz with constant `1`, unrestricted
  bilinearity), which is why the fixed bundle
  (`Submission/Work/FTS/GalerkinFix/Defs.lean`) uses `Work.FTS.Nonlin.UnifIP` instead.
* **The Galerkin scheme** — the test sequence `φ`, the coefficient vectors `c : Fin n → ℝ`, the
  finite linear combinations `galFun φ c`, the family `galFam`, the projected right hand side
  `galRHS`, the projected vector field `galField`, the projected evolution equation
  `IsGalerkinCoeff` (an ODE in the finite-dimensional space `Fin n → ℝ`), the projection of the
  datum `coeffOf`.
* **The convergence vocabulary** of the compactness step: `ConvPoint` (pointwise on the open
  quadrant for `τ ≥ 0`) and the stronger `ConvLocUnif` (uniform on compact subsets), which is what
  the paper's Arzelà–Ascoli/weak-compactness step produces (`convLocUnif_convPoint`).

The *a-priori input bundle* `DynInputs`, the density statement `DenseSpan` and the data class
`DataAdm` have moved (2026-10-03 interface fix) to
`Submission/Work/FTS/GalerkinFix/Defs.lean`, where they are stated in the frozen vocabulary
`Submission/Work/FTS/Vocab.lean` (`RegQ`, `UnifIP`, `GalBasis`, `PsiCan`, `ProfileEquicont`).

## Conventions

Functions of the self-similar variables are curried `f z θ` (`Fn = ℝ → ℝ → ℝ`), families are
`g z θ τ` (`Fam = ℝ → ℝ → ℝ → ℝ`), and all integrals are over `[0,∞) × [0,π/2]` with the measure
`dz dθ` (the Warning of §Notation of the paper: **not** `z dz dθ`) — the convention of
`Submission/Work/Spaces`, `Work.FM`, `Work.Elliptic`, `Work.Coercivity`, `Work.Construction`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Stability.Cutoff
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## Families of fake-time profiles -/

/-- A function of the self-similar variables `(z,θ)` on the quadrant `[0,∞) × [0,π/2]`. -/
abbrev Fn : Type := ℝ → ℝ → ℝ

/-- A family `(z,θ,τ) ↦ g z θ τ` of fake-time profiles. -/
abbrev Fam : Type := ℝ → ℝ → ℝ → ℝ

/-- `slice g τ` is the profile `g(·,·,τ)` of a family. -/
def slice (g : Fam) (τ : ℝ) : Fn := fun z θ => g z θ τ

@[simp] theorem slice_apply (g : Fam) (τ z θ : ℝ) : slice g τ z θ = g z θ τ := rfl

/-- The family generated by a curve `τ ↦ G τ` of profiles. -/
def famOf (G : ℝ → Fn) : Fam := fun z θ τ => G τ z θ

@[simp] theorem slice_famOf (G : ℝ → Fn) (τ : ℝ) : slice (famOf G) τ = G τ := rfl

theorem slice_inj {g g' : Fam} (h : ∀ τ, slice g τ = slice g' τ) : g = g' := by
  funext z θ τ; exact congrFun (congrFun (h τ) z) θ

/-- The fake-time derivative `∂_τ g(·,·,τ)`. -/
def gdot (g : Fam) (τ : ℝ) : Fn := fun z θ => deriv (fun s => g z θ s) τ

/-- `slice` commutes with subtraction. -/
theorem slice_sub (g g' : Fam) (τ : ℝ) : slice (fun z θ s => g z θ s - g' z θ s) τ
    = fun z θ => slice g τ z θ - slice g' τ z θ := rfl

/-! ## The abstract ODE vocabulary used by the Galerkin scheme

The Galerkin scheme of the audit (§4 N6, steps 2–4) reduces the fake-time equation to an ordinary
differential equation in the finite-dimensional space `Fin n → ℝ` of Fourier coefficients; the two
notions below are the abstract solution predicates of that ODE, for an arbitrary normed space `E`.
They live here (and not in `ODE.lean`) only so that the interface `DynInputs` can mention them. -/

/-- `α` solves the ODE `ẋ = f(t,x)` on the closed interval `[0,T]` with `α 0 = x₀`: the derivative
is taken *within* `[0,T]`, so no behaviour of `α` outside the interval is asserted. -/
def IsSolOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E → E) (x₀ : E)
    (T : ℝ) (α : ℝ → E) : Prop :=
  α 0 = x₀ ∧ ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt α (f t (α t)) (Set.Icc 0 T) t

/-- `α` solves the ODE `ẋ = f(t,x)` on the whole half-line `[0,∞)` with `α 0 = x₀`: the derivative
is taken within `Set.Ici 0`, the honest formulation of an evolution equation posed for `τ ≥ 0`. -/
def IsSolGlob {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E → E) (x₀ : E)
    (α : ℝ → E) : Prop :=
  α 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivWithinAt α (f t (α t)) (Set.Ici 0) t

theorem IsSolOn.apply_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {x₀ : E} {T : ℝ} {α : ℝ → E} (h : IsSolOn f x₀ T α) : α 0 = x₀ := h.1

/-- The half-line equation restricted to a finite interval. -/
theorem IsSolGlob.isSolOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E}
    {x₀ : E} {α : ℝ → E} (h : IsSolGlob f x₀ α) (T : ℝ) : IsSolOn f x₀ T α :=
  ⟨h.1, fun t ht => (h.2 t ht.1).mono (fun s hs => hs.1)⟩

/-- A solution on `[0,T']` is a solution on every shorter interval `[0,T]`. -/
theorem IsSolOn.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E}
    {x₀ : E} {α : ℝ → E} {T T' : ℝ} (h : IsSolOn f x₀ T' α) (hTT' : T ≤ T') :
    IsSolOn f x₀ T α :=
  ⟨h.1, fun t ht => (h.2 t ⟨ht.1, le_trans ht.2 hTT'⟩).mono (fun s hs => ⟨hs.1, le_trans hs.2 hTT'⟩)⟩

/-! ## The dynamic modulated equation -/

/-- The `τ`-dependent modulation constant of the fake-time equation,
`μ̄(τ) = (1/(2α))(L₁₂(N₀)(0)+L₁₂(N)(0)) + (1/(2α))L₁₂(3D_θg/(1+z))(0)` evaluated on the family
`g` and its stream function `Φ`: the paper's `μ` of §Modulation, made `τ`-dependent, **with the
sign of the transport zero-mode forced by `LGammaT_eq`** (`FTS_MUFUN_SIGN.md` §5, option (a')).

It is `Construction.mufunS`, i.e. `2α·muDyn = μ̄ + L₁₂(Transport g)(0)`
(`Work.Construction.two_mul_mufunS`), *not* the paper-display `Construction.mufun`.  This is
what makes the dynamic profile equation `(E)` hold identically
(`Work.FTS.MeridianDyn.DynEqF`). -/
def muDyn (α : ℝ) (Φ g : Fam) (τ : ℝ) : ℝ :=
  Construction.mufunS α (Construction.N0 α (Construction.Ftau α g τ) (slice g τ))
    (Construction.N α (Construction.Ftau α g τ) (slice Φ τ)) (slice g τ)

/-- The paper's second modulation constant `λ(τ) = -2μ̄(τ)/(1+μ̄(τ))`. -/
def lamDyn (α : ℝ) (Φ g : Fam) (τ : ℝ) : ℝ := Construction.lamfun (muDyn α Φ g τ)

/-- The linear part `-𝓛_Γ^T g(τ)` of the fake-time equation. -/
def dynLin (α : ℝ) (g : Fam) (τ : ℝ) : Fn :=
  fun z θ => -(Coercivity.LGammaT α (slice g τ) z θ)

/-- The nonlinear part of the fake-time equation:
`-μ̄(τ)(Γ/c)2z²/(1+z)³ + N₀ + N + N_*`, evaluated at the τ-dependent modulation constants. -/
def dynRHS (α : ℝ) (Φ g : Fam) (τ : ℝ) : Fn :=
  Construction.gRHS α (muDyn α Φ g τ) (lamDyn α Φ g τ)
    (Construction.Ftau α g τ) (slice Φ τ) (slice g τ)

/-- **The dynamic modulated equation**, in its honest half-line form: for every `τ ≥ 0` and every
point of the open quadrant,
`∂_τ g = -𝓛_Γ^T(g) + gRHS(μ̄(τ), λ(τ), F_*+g(τ), Φ(τ), g(τ))`,
the derivative being taken within `Set.Ici 0` (the equation is only posed for `τ ≥ 0`; no
behaviour at or past the blow-up time of the physical problem is assumed anywhere). -/
def IsDynEqOn (α : ℝ) (Φ g : Fam) : Prop :=
  ∀ z θ τ, 0 ≤ τ → (z, θ) ∈ Construction.Qd →
    HasDerivWithinAt (fun s => g z θ s) (dynLin α g τ z θ + dynRHS α Φ g τ z θ) (Set.Ici 0) τ

/-- The dynamic modulated equation in the two-sided form used by the audit
(`HasDerivAt` at every `τ ≥ 0`, including `τ = 0`).  It is *stronger* than `IsDynEqOn`
(`isDynEqOn_of_isDynEq`): it asks for the derivative also from the left at `τ = 0`. -/
def IsDynEq (α : ℝ) (Φ g : Fam) : Prop :=
  ∀ z θ τ, 0 ≤ τ → (z, θ) ∈ Construction.Qd →
    HasDerivAt (fun s => g z θ s) (dynLin α g τ z θ + dynRHS α Φ g τ z θ) τ

theorem isDynEqOn_of_isDynEq {α : ℝ} {Φ g : Fam} (h : IsDynEq α Φ g) : IsDynEqOn α Φ g :=
  fun z θ τ hτ hz => (h z θ τ hτ hz).hasDerivWithinAt

theorem isDynEq_of_isDynEqOn_pos {α : ℝ} {Φ g : Fam} (h : IsDynEqOn α Φ g) :
    ∀ z θ τ, 0 < τ → (z, θ) ∈ Construction.Qd →
      HasDerivAt (fun s => g z θ s) (dynLin α g τ z θ + dynRHS α Φ g τ z θ) τ :=
  fun z θ τ hτ hz =>
    (h z θ τ hτ.le hz).hasDerivAt (Ici_mem_nhds hτ)

/-- The two modulation constants of the dynamic equation agree with `Construction.mufunS`,
`Construction.lamfun` term by term. -/
theorem muDyn_eq (α : ℝ) (Φ g : Fam) (τ : ℝ) :
    muDyn α Φ g τ
      = Construction.mufunS α (Construction.N0 α (Construction.Ftau α g τ) (slice g τ))
          (Construction.N α (Construction.Ftau α g τ) (slice Φ τ)) (slice g τ) := rfl

theorem lamDyn_eq (α : ℝ) (Φ g : Fam) (τ : ℝ) :
    lamDyn α Φ g τ = -2 * muDyn α Φ g τ / (1 + muDyn α Φ g τ) := rfl

theorem dynRHS_eq (α : ℝ) (Φ g : Fam) (τ : ℝ) :
    dynRHS α Φ g τ
      = Construction.gRHS α (muDyn α Φ g τ) (lamDyn α Φ g τ)
          (Construction.Ftau α g τ) (slice Φ τ) (slice g τ) := rfl

/-! ## The elliptic law and packaged solutions -/

/-- The elliptic (Biot–Savart) law on the open quadrant, in the `F`-side convention
`bslOp α Φ = F` (i.e. `Construction.StatEqPhi` restricted to `Qd`).  It is passed as an explicit
parameter `Law` to `IsDynGSolWith`, so that the convention pinned by N1
(audit §4 N1: `bslOp p Φ = -F` is the convention consistent with `Work.Cyl.vorticity_psiField`)
can be substituted without touching this area: pass `fun F Φ => ∀ z θ, (z,θ) ∈ Qd → bslOp α Φ z θ = -F z θ`. -/
def EllLaw (α : ℝ) : Fn → Fn → Prop :=
  fun F Φ => ∀ z θ, (z, θ) ∈ Construction.Qd → Elliptic.bslOp α Φ z θ = F z θ

/-- **A solution of the dynamic modulated problem** with an *explicit* elliptic law `Law`:
the elliptic law holds at every `τ ≥ 0` for the profile `F_* + g(τ)` and its stream function
`Φ(τ)`, and the dynamic equation holds.  This is the form in which the existence theorem of this
area is stated. -/
def IsDynGSolWith (Law : Fn → Fn → Prop) (α : ℝ) (Φ g : Fam) : Prop :=
  (∀ τ, 0 ≤ τ → Law (Construction.Ftau α g τ) (slice Φ τ)) ∧ IsDynEqOn α Φ g

/-- The same, with the two-sided equation `IsDynEq` (the audit's `IsDynGSol` field). -/
def IsDynGSolWithStrong (Law : Fn → Fn → Prop) (α : ℝ) (Φ g : Fam) : Prop :=
  (∀ τ, 0 ≤ τ → Law (Construction.Ftau α g τ) (slice Φ τ)) ∧ IsDynEq α Φ g

/-- A solution of the dynamic modulated problem with the concrete elliptic law `EllLaw α`. -/
def IsDynGSolOn (α : ℝ) (Φ g : Fam) : Prop := IsDynGSolWith (EllLaw α) α Φ g

/-- A solution of the dynamic modulated problem with the concrete elliptic law `EllLaw α`, in the
two-sided form of the audit. -/
def IsDynGSol (α : ℝ) (Φ g : Fam) : Prop := IsDynGSolWithStrong (EllLaw α) α Φ g

theorem isDynGSolWithStrong.isDynGSolWith {Law : Fn → Fn → Prop} {α : ℝ} {Φ g : Fam}
    (h : IsDynGSolWithStrong Law α Φ g) : IsDynGSolWith Law α Φ g :=
  ⟨h.1, isDynEqOn_of_isDynEq h.2⟩

theorem isDynGSol_isDynGSolOn {α : ℝ} {Φ g : Fam} (h : IsDynGSol α Φ g) :
    IsDynGSolOn α Φ g :=
  isDynGSolWithStrong.isDynGSolWith h

/-! ## Admissible data and the regularity package -/

/- The admissible-datum class `DataAdm` moved, in the 2026-10-03 interface fix, to
`Submission/Work/FTS/GalerkinFix/Defs.lean`: the delivered class asked for `Coercivity.HkAdm`,
which contains the analyticity hypothesis `Work.Spaces.SmoothNbhd`, so it is not satisfied by the
localised datum of the route nor by any PDE object.  Its replacement
`Work.FTS.Galerkin.DataAdm α g₀ = LocData.DataAdm α g₀ ∧ L₁₂(g₀)(0) = 0 ∧ RegQ α 5 g₀` is defined
in the fixed interface (design §1.2). -/

/-- **The regularity package** of a solution family `g` of the dynamic modulated equation: smooth
on the interior of the fake-time slab, jointly continuous in `τ` up to `τ = 0`, with `ℋ⁴`- and
`ℋ⁵`-membership at every `τ ≥ 0`, `ℋ³`-membership of `∂_τg`, and vanishing on the angular
boundaries.  This is the interface consumed by N7 (regularity transfer) and N8 (physical
reconstruction): it is *interior* regularity only, uniformly in `τ ≥ 0`, and asserts nothing at or
past the physical blow-up time. -/
structure RegPkg (α : ℝ) (g : Fam) : Prop where
  /-- joint smoothness on the interior of the quadrant, for all fake times near `[0,∞)`; the order
  is `Work.Stability.smoothOrder = ∞` (interior `C^∞`), **not** the analytic order `⊤` of the
  delivered version (which no solution of the equation satisfies — see the interface fix of
  2026-10-03, `Submission/Work/FTS/GalerkinFix/`). -/
  smooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi (-1))
  /-- joint continuity in `τ` up to `τ = 0`, at every point of the open quadrant. -/
  cont : ∀ z θ, (z, θ) ∈ Construction.Qd → ContinuousOn (fun τ => g z θ τ) (Set.Ici 0)
  /-- `ℋ⁴`-membership at every `τ ≥ 0`. -/
  mem4 : ∀ τ, 0 ≤ τ → Spaces.HkMem α 4 (slice g τ)
  /-- `ℋ⁵`-membership at every `τ ≥ 0`. -/
  mem5 : ∀ τ, 0 ≤ τ → Spaces.HkMem α 5 (slice g τ)
  /-- `ℋ³`-membership of the fake-time derivative at every `τ ≥ 0`. -/
  deriv3 : ∀ τ, 0 ≤ τ → Spaces.HkMem α 3 (gdot g τ)
  /-- vanishing on the angular boundaries at every `τ ≥ 0`. -/
  vanish : ∀ τ, 0 ≤ τ → Spaces.VanishTheta (slice g τ)

/-! ## The `ℋ⁴` inner product -/

/-- **The `ℋ⁴` inner product** of the audit (N2): the paper's admissible inner product
`Construction.IsH4IP` together with the symmetry `IP f g = IP g f`.

Symmetry is not implied by `IsH4IP`, but it *is* automatic for the paper's inner product: the
inductive construction (`Work.Coercivity.H1IP`, `HkIPStep`) starts from the symmetric `wip`s and
adds symmetric terms, so every inner product produced by the induction of §"Higher order
derivatives and the inner product on `ℋ^k`" is symmetric.  Symmetry is exactly what turns the
`IP`-orthonormality of the Galerkin basis into the *exactness of the energy identity*
(`IP (galFun φ c) (galFun φ c) = ∑ₖ cₖ²`), which is the point of the audit's step 4. -/
structure IsH4Inner (α : ℝ) (IP : Fn → Fn → ℝ) : Prop extends Construction.IsH4IP α IP where
  /-- `IP` is symmetric. -/
  symm : ∀ f g : Fn, IP f g = IP g f

theorem IsH4Inner.toIsHkIP {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) :
    Coercivity.IsHkIP α 4 IP := h.isHkIP

/-- Bilinearity in the second argument, derived from symmetry and `IsH4IP.smul_fst`. -/
theorem IsH4Inner.smul_snd {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP)
    (c : ℝ) (f g : Fn) : IP f (fun z θ => c * g z θ) = c * IP f g := by
  rw [h.symm, h.smul_fst, h.symm]

/-! ## The Galerkin scheme -/

/-- The finite linear combination `∑_{k : Fin n} c k · φ (k : ℕ)` of test functions. -/
def galFun (φ : ℕ → Fn) {n : ℕ} (c : Fin n → ℝ) : Fn :=
  fun z θ => ∑ k : Fin n, c k * φ (k : ℕ) z θ

/-- The Galerkin family with coefficient curve `τ ↦ c τ`. -/
def galFam (φ : ℕ → Fn) (n : ℕ) (c : ℝ → Fin n → ℝ) : Fam :=
  fun z θ τ => galFun φ (c τ) z θ

@[simp] theorem galFam_apply (φ : ℕ → Fn) (n : ℕ) (c : ℝ → Fin n → ℝ) (z θ τ : ℝ) :
    galFam φ n c z θ τ = galFun φ (c τ) z θ := rfl

@[simp] theorem slice_galFam (φ : ℕ → Fn) (n : ℕ) (c : ℝ → Fin n → ℝ) (τ : ℝ) :
    slice (galFam φ n c) τ = galFun φ (c τ) := rfl

/-- The projection of a datum onto the first `n` modes: `(coeffOf IP g₀ φ n) k = IP g₀ (φ k)`.
For an `IP`-orthonormal sequence this is the coefficient of `φ k` in the `IP`-projection of `g₀`
onto the span of the first `n` test functions. -/
def coeffOf (IP : Fn → Fn → ℝ) (g₀ : Fn) (φ : ℕ → Fn) (n : ℕ) : Fin n → ℝ :=
  fun k => IP g₀ (φ (k : ℕ))

/-- The right hand side of the projected (weak) Galerkin equation, as a function of the
coefficient vector `c`: `-𝓛_Γ^T gₙ + gRHS(μ̄,λ,F_*+gₙ,Ψ(gₙ),gₙ)` evaluated on
`gₙ = ∑ c k φ k`.  The stream function of the Galerkin profile is `Ψ (galFam φ n c)`, where `Ψ` is
the stream-function assignment of N1 (`Work.Elliptic.exists_bslSol` / `bslSol_unique`). -/
def galRHS (α : ℝ) (φ : ℕ → Fn) (n : ℕ) (Psi : Fam → Fam) (τ : ℝ) (c : Fin n → ℝ) : Fn :=
  dynLin α (galFam φ n (fun _ => c)) τ
    + dynRHS α (Psi (galFam φ n (fun _ => c))) (galFam φ n (fun _ => c)) τ

/-- The **projected (Galerkin) vector field** in `ℝⁿ`: the `k`-th component is the `IP`-pairing of
the projected right hand side with the `k`-th test function.  The Galerkin scheme of the audit's
step 3 is the ordinary differential equation `ċ = galField(τ, c)` in `Fin n → ℝ`. -/
def galField (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) (n : ℕ) (Psi : Fam → Fam) (τ : ℝ)
    (c : Fin n → ℝ) : Fin n → ℝ :=
  fun k => IP (galRHS α φ n Psi τ c) (φ (k : ℕ))

/-- **The projected evolution equation** (the Galerkin ODE, audit step 3): the coefficient curve
`solves the fake-time equation tested against the first `n` modes, in the strong form of an ODE in
`Fin n → ℝ`.  Its equivalence with the weak (tested) form is `isGalerkinCoeff_iff_weak`
(`Submission/Work/FTS/Galerkin/Projection.lean`), which uses the `IP`-orthonormality of the basis. -/
def IsGalerkinCoeff (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) (n : ℕ) (Psi : Fam → Fam)
    (c : ℝ → Fin n → ℝ) : Prop :=
  ∀ τ, 0 ≤ τ → HasDerivWithinAt (fun s => c s) (galField α IP φ n Psi τ (c τ)) (Set.Ici 0) τ

theorem isGalerkinCoeff_iff {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} {n : ℕ}
    {Psi : Fam → Fam} {c : ℝ → Fin n → ℝ} :
    IsGalerkinCoeff α IP φ n Psi c ↔
      ∀ τ, 0 ≤ τ → HasDerivWithinAt (fun s => c s) (galField α IP φ n Psi τ (c τ))
        (Set.Ici 0) τ := Iff.rfl

/-- A global solution of the Galerkin ODE is a coefficient curve solving the projected
evolution equation, and conversely. -/
theorem isGalerkinCoeff_iff_isSolGlob {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} {n : ℕ}
    {Psi : Fam → Fam} {c : ℝ → Fin n → ℝ} {x₀ : Fin n → ℝ} (h0 : c 0 = x₀) :
    IsGalerkinCoeff α IP φ n Psi c ↔ IsSolGlob (galField α IP φ n Psi) x₀ c :=
  ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩

/- The density statement `DenseSpan` moved, in the 2026-10-03 interface fix, to
`Submission/Work/FTS/GalerkinFix/Defs.lean`, with the corrected class `RegQ α 4` and the vanishing
of the zero mode in place of `Coercivity.HkAdm` (design §1.2).  Its now-frozen name is
`Work.FTS.Galerkin.DenseSpan α IP φ`, with `IP : ℝ → Fn → Fn → ℝ` as the (curried) inner product.
-/

/-! ## Convergence of families (the compactness step) -/

/-- Pointwise convergence of a sequence of families to a limit family, on the **closed** quadrant
`[0,∞) × [0,π/2]` and for every `τ ≥ 0`.  Convergence on the closed quadrant (and not only on the
open one) is the form the passage to the limit needs: the nonlinear terms of the equation are
functionals of `g` (`L₁₂` integrates `g` over all of `Iθ`, including the angular boundary), so the
limit function has to be identified everywhere on `Iz × Iθ`, not merely almost everywhere.  This is
the convergence consumed by `DynInputs.hLimit`. -/
def ConvPoint (G : ℕ → Fam) (g : Fam) : Prop :=
  ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, ∀ τ, 0 ≤ τ →
    Tendsto (fun n => G n z θ τ) atTop (𝓝 (g z θ τ))

/-- The closed fake-time slab `[0,∞) × [0,π/2] × [0,∞)` of the self-similar variables `(z,θ)` and
the fake time `τ`. -/
def Slab : Set (ℝ × ℝ × ℝ) := {p | p.1 ∈ Spaces.Iz ∧ p.2.1 ∈ Spaces.Iθ ∧ 0 ≤ p.2.2}

theorem mem_Slab {p : ℝ × ℝ × ℝ} :
    p ∈ Slab ↔ p.1 ∈ Spaces.Iz ∧ p.2.1 ∈ Spaces.Iθ ∧ 0 ≤ p.2.2 := Iff.rfl

/-- The slab is closed in `ℝ³`. -/
theorem isClosed_Slab : IsClosed Slab := by
  have h1 : IsClosed {p : ℝ × ℝ × ℝ | p.1 ∈ Set.Ici (0 : ℝ)} :=
    isClosed_Ici.preimage continuous_fst
  have h2 : IsClosed {p : ℝ × ℝ × ℝ | p.2.1 ∈ Set.Icc (0 : ℝ) (Real.pi / 2)} :=
    isClosed_Icc.preimage (continuous_fst.comp continuous_snd)
  have h3 : IsClosed {p : ℝ × ℝ × ℝ | (0 : ℝ) ≤ p.2.2} :=
    isClosed_Ici.preimage (continuous_snd.comp continuous_snd)
  have h4 : Slab = {p : ℝ × ℝ × ℝ | p.1 ∈ Set.Ici (0 : ℝ)}
      ∩ {p : ℝ × ℝ × ℝ | p.2.1 ∈ Set.Icc (0 : ℝ) (Real.pi / 2)}
      ∩ {p : ℝ × ℝ × ℝ | (0 : ℝ) ≤ p.2.2} := by
    ext p
    simp only [Slab, Set.mem_setOf_eq, Set.mem_inter_iff, Spaces.Iz, Spaces.Iθ]
    tauto
  rw [h4]
  exact (h1.inter h2).inter h3

def ConvLocUnif (G : ℕ → Fam) (g : Fam) : Prop :=
  ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab →
    TendstoUniformlyOn (fun n (p : ℝ × ℝ × ℝ) => G n p.1 p.2.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) atTop K

/-! ## The a-priori input bundle -/

/-- **The weak (tested) form of the dynamic modulated equation**: for every test function `φ k` and
every `τ ≥ 0`, the scalar function `τ ↦ IP (g(τ)) (φ k)` has the derivative obtained by pairing the
right hand side of the dynamic equation with `φ k`. -/
def IsDynWeakOn (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) (g Φ : Fam) : Prop :=
  ∀ (k : ℕ) (τ : ℝ), 0 ≤ τ →
    HasDerivWithinAt (fun s => IP (slice g s) (φ k))
      (IP (dynLin α g τ + dynRHS α Φ g τ) (φ k)) (Set.Ici 0) τ

/-- **The weak form determines the equation** (the fundamental lemma of the calculus of variations
for the Galerkin span): if `g` satisfies the tested form against every test function, then it
satisfies the dynamic equation pointwise on the open quadrant.  It is discharged from
`DynInputs.hφ_dense` (density of the span) together with the identification of `IP` with its integral
form on the span. -/
def WeakDetermines (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ g Φ : Fam, IsDynWeakOn α IP φ g Φ → IsDynEqOn α Φ g

/-- The profile of the `n`-th Galerkin family at the point `p = (z, θ, τ)`. -/
def prof (φ : ℕ → Fn) (c : ∀ n : ℕ, ℝ → Fin n → ℝ) (n : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  galFun φ (c n p.2.2) p.1 p.2.1

/-- The hypothesis that `c` is a family of Galerkin solutions in the a-priori ball: each truncation
solves its projected evolution equation and its coefficients stay in the ball of radius `R`. -/
def IsGalFam (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) (Psi : Fam → Fam) (R : ℝ)
    (c : ∀ n : ℕ, ℝ → Fin n → ℝ) : Prop :=
  (∀ n : ℕ, IsGalerkinCoeff α IP φ n Psi (c n)) ∧
    (∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → ∑ k : Fin n, (c n τ k) ^ 2 ≤ R ^ 2)

/- The structure `DynInputs` moved, in the 2026-10-03 interface fix, to
`Submission/Work/FTS/GalerkinFix/Defs.lean`, with the corrected field list of design §1.2–1.3:
`hLimBound` in place of `hApriori`, `Work.FTS.Nonlin.UnifIP` in place of `IsH4Inner`,
truncation-dependent Lipschitz/bound constants, the canonical stream-function operator `PsiCan`,
the basis class `GalBasis`, `ProfileEquicont` in place of `hProfileLip`, and the corrected data
class `DataAdm`.  Its now-frozen name is `Work.FTS.Galerkin.DynInputs`. -/


end Work.FTS.Galerkin
