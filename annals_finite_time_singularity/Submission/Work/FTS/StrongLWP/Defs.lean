/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongLWP/` — the strong-solution (local well-posedness) area, S1/S3 of
`FTS_STRONG_ROUTE.md` §3

Design document: `Submission/Work/FTS/FTS_STRONG_ROUTE.md` §3.  The lead's route replaces the
"limit of the IP₄-Galerkin scheme" step (whose limit cannot be shown to have the regularity the
downstream consumers need — obstructions 1–3 of the design) by a **strong-solution** route:

| # | item | statement | status |
|---|---|---|---|
| S1 | `lwp_H6` | `RegQ α 6 g₀` ⟹ `∃ T > 0, ∃ Φ g`, `IsDynGSolWith (IsBslSolPos α) α Φ g`, `g(·,·,0) = g₀`, `HkMem α 6` and a uniform `ℋ⁶`-bound on `[0,T]` | target |
| S2 | `persist_H6` | a strong solution with `sup Xn₄ < ∞` has `sup Xn₆ < ∞` | target |
| S3 | `sobolev_C4` | `HkMem α 6 f` ⟹ C⁴ control on the open quadrant | **corrected**, see below |
| S4 | `apriori_strong` | `Xn₄(g₀) ≤ α²` ⟹ `Xn₄ ≤ C₀α²` on the whole interval | target |
| S5 | `global_strong` | S1+S2+S4 ⟹ global strong solution with `RegPkgMin` and the `ℋ⁴`-bound | target |
| S6 | `dbd_of_eq` | `‖dynLin + dynRHS‖_{ℋ³} ≤ C(Xn₄)` | target |

## What this module fixes

* **`IsBslSolPos`** — the *positivised* elliptic law of the strong route: the paper's (PolarBSL)
  on the open quadrant, with the Dirichlet data asserted only for `z ≥ 0`.  The frozen
  `Work.Elliptic.IsBslSol` asserts `Ψ z 0 = 0` and `Ψ z (π/2) = 0` for **all** `z ∈ ℝ`, which a
  solution of the local problem (whose data are only given on `Iz`) does not satisfy; the audit
  `FTS_INTEGRATION_AUDIT.md` §3 lists exactly this as one of the traps ("`RegPkg.vanish` (all
  `z`)").  `IsBslSolPos` is the `Law` to pass to `IsDynGSolWith`.
* **`RegPkgMin`** — the regularity package of the strong route, *verbatim* as in the design §3
  (finite order `4` instead of `C^∞`, no `mem5`, no `τ < 0` region, `vanish` only for `z ≥ 0`).
  It is the interface `RegPkgGal` was asked to switch to, and the input of S5.
* **`RegPkgH6`** — `RegPkgMin` together with the order-`6` membership and a uniform `ℋ⁶`-bound on
  `[0,T]`: the conclusion of S1/S2 and the input of the continuation argument S5.
* **`Xn6`** — the size `|g|_{ℋ⁶}` (the order-`6` companion of `Work.FTS.Nonlin.Xn`).
* **`LWPSol`** — the bundled conclusion of S1 (all four clauses at once).

Nothing here is a reduction of the main theorems to new axioms: the definitions below are
*vocabulary* for the chapter (`IsBslSolPos`, `RegPkgMin`, `RegPkgH6`, `Xn6`), and the theorems
about them are proved in `Submission/Work/FTS/StrongLWP/Basic.lean` and in the subdirectories of
this area.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP

open Work.FTS.Galerkin (Fn Fam slice gdot IsDynGSolWith IsDynEqOn dynLin dynRHS)

set_option autoImplicit false

/-! ## The elliptic law `IsBslSolPos` -/

/-- **The positivised elliptic (Biot–Savart) law of the strong route.**

`IsBslSolPos α F Ψ` is the paper's (PolarBSL) problem

  `α²z²∂_zzΨ + α(5+α)z∂_zΨ - Lzero Ψ = F`  on the open quadrant `z > 0`, `0 < θ < π/2`,

together with

* the Dirichlet data `Ψ z 0 = Ψ z (π/2) = 0` **only for `z ≥ 0`** (the frozen `IsBslSol` asks it for
  every real `z`, which no solution of the local problem with data on `Iz` satisfies — audit
  `FTS_INTEGRATION_AUDIT.md` §3, the `Slab`-pinning trap), and
* the decay `Ψ z θ → 0` as `z → ∞`, for every `θ ∈ Iθ`.

This is the `Law` argument of `IsDynGSolWith` in the strong-solution route: the local solution of
S1 is only defined for `z ≥ 0`, so the two identifications at `θ = 0, π/2` are only known there. -/
def IsBslSolPos (α : ℝ) (F Ψ : Fn) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
    (∀ z, 0 ≤ z → Ψ z 0 = 0 ∧ Ψ z (π / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))

/-- `IsBslSolPos` is the frozen `IsBslSol` with the two boundary conditions weakened to `z ≥ 0`:
this is the direction a caller holding the frozen law uses. -/
theorem isBslSolPos_of_isBslSol {α : ℝ} {F Ψ : Fn}
    (h : Work.Elliptic.IsBslSol α F Ψ) : IsBslSolPos α F Ψ :=
  ⟨h.1, fun z _ => ⟨h.2.1 z, h.2.2.1 z⟩, h.2.2.2⟩

/-- The equation clause of `IsBslSolPos`, on the open quadrant. -/
theorem IsBslSolPos.eq {α : ℝ} {F Ψ : Fn} (h : IsBslSolPos α F Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α Ψ z θ = F z θ := h.1 z hz θ hθ hθ2

/-- The Dirichlet data of `IsBslSolPos`, for `z ≥ 0`. -/
theorem IsBslSolPos.boundary {α : ℝ} {F Ψ : Fn} (h : IsBslSolPos α F Ψ)
    {z : ℝ} (hz : 0 ≤ z) : Ψ z 0 = 0 ∧ Ψ z (π / 2) = 0 := h.2.1 z hz

/-- The far-field decay of `IsBslSolPos`. -/
theorem IsBslSolPos.tendsto {α : ℝ} {F Ψ : Fn} (h : IsBslSolPos α F Ψ) :
    ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0) := h.2.2

/-! ## The regularity package `RegPkgMin` (design §3, verbatim) -/

/-- **The regularity package of the strong-solution route** — `FTS_STRONG_ROUTE.md` §3, copied
verbatim.

It is what the physical bridge (`RegPkgGal`, design §4) consumes: joint `C¹` in `(z,τ)`, `C⁴` at
every `τ ≥ 0`, continuity in `τ` up to `τ = 0` at every point of the open quadrant, `ℋ⁴`-membership
at every `τ ≥ 0`, a uniform `ℋ³`-bound on `∂_τg` for `τ > 0`, and vanishing on the angular
boundaries for `z ≥ 0`.

Compared with the frozen `Work.FTS.Galerkin.RegPkg` it drops: the `τ ∈ (-1,0)` region, the `z < 0`
half-line, the `C^∞` smoothness (replaced by `C⁴`), and the `ℋ⁵`-membership (`mem5`); nothing
downstream of `RegPkgGal` uses any of them (design §1). -/
structure RegPkgMin (α : ℝ) (g : Fam) : Prop where
  /-- joint `C¹` in the interior of the quadrant, for every fake time `τ > 0`. -/
  c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0)
  /-- `C⁴` in the space variables at every `τ ≥ 0`. -/
  c4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0
  /-- continuity in the fake time up to `τ = 0`, at every point of the open quadrant. -/
  cont : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ContinuousOn (fun τ => g z θ τ) (Set.Ici 0)
  /-- `ℋ⁴`-membership at every `τ ≥ 0`. -/
  mem4 : ∀ τ, 0 ≤ τ → Work.Spaces.HkMem α 4 (slice g τ)
  /-- a uniform `ℋ³`-bound on the fake-time derivative, for `τ > 0`. -/
  dbd : ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
    Work.Spaces.HkMem α 3 (gdot g τ) ∧ Work.Spaces.HkNorm α 3 (gdot g τ) ≤ Cd
  /-- vanishing on the angular boundaries, for `z ≥ 0`. -/
  vanish : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0

theorem RegPkgMin.c1' {α : ℝ} {g : Fam} (h : RegPkgMin α g) : ContDiffOn ℝ 1
    (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0) := h.c1

theorem RegPkgMin.cont' {α : ℝ} {g : Fam} (h : RegPkgMin α g) {z θ : ℝ}
    (hz : (z, θ) ∈ Work.Construction.Qd) :
    ContinuousOn (fun τ => g z θ τ) (Set.Ici 0) := h.cont z θ hz

/-! ## The order-`6` size `Xn6`, and the `ℋ⁶`-package `RegPkgH6` -/

/-- The size `|g|_{ℋ⁶}` of the strong-solution route (the order-`6` companion of
`Work.FTS.Nonlin.Xn`). -/
abbrev Xn6 (α : ℝ) (g : Fn) : ℝ := Work.Spaces.HkNorm α 6 g

/-- The order-`4` size, under the name used by this chapter.  It is *definitionally*
`Work.FTS.Nonlin.Xn α g`. -/
abbrev Xn4 (α : ℝ) (g : Fn) : ℝ := Work.Spaces.HkNorm α 4 g

theorem Xn4_eq_Xn (α : ℝ) (g : Fn) : Xn4 α g = Work.FTS.Nonlin.Xn α g := rfl

/-- **The `ℋ⁶`-package of a strong solution on `[0,T]`**: `RegPkgMin`, order-`6` membership and a
uniform `ℋ⁶`-bound on the interval.  This is the conclusion of S1 and of the persistence theorem
S2, and the input of the continuation argument S5. -/
structure RegPkgH6 (α : ℝ) (T : ℝ) (g : Fam) : Prop where
  /-- the finite-order regularity package of the strong route. -/
  min : RegPkgMin α g
  /-- `ℋ⁶`-membership at every `τ ∈ [0,T]`. -/
  mem6 : ∀ τ, 0 ≤ τ → τ ≤ T → Work.Spaces.HkMem α 6 (slice g τ)
  /-- a uniform `ℋ⁶`-bound on `[0,T]`. -/
  bd6 : ∃ C, ∀ τ, 0 ≤ τ → τ ≤ T → Xn6 α (slice g τ) ≤ C

theorem RegPkgH6.toRegPkgMin {α T : ℝ} {g : Fam} (h : RegPkgH6 α T g) : RegPkgMin α g := h.min

theorem RegPkgH6.mem6' {α T : ℝ} {g : Fam} (h : RegPkgH6 α T g) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) : Work.Spaces.HkMem α 6 (slice g τ) := h.mem6 τ hτ hτT

theorem RegPkgH6.bd6' {α T : ℝ} {g : Fam} (h : RegPkgH6 α T g) :
    ∃ C, ∀ τ, 0 ≤ τ → τ ≤ T → Xn6 α (slice g τ) ≤ C := h.bd6

/-! ## The bundled conclusion of S1 -/

/-- The dynamic modulated equation restricted to the interval `[0,T]`: the within-derivative on
`[0,T]` of the `τ`-slice of `g` equals the RHS.  It is the local form needed by a local
well-posedness statement (which asserts nothing beyond `T`); the frozen `IsDynEqOn` is the same
statement for all `τ ≥ 0`. -/
def IsDynEqOnT (α : ℝ) (T : ℝ) (Φ g : Fam) : Prop :=
  ∀ τ, 0 ≤ τ → τ ≤ T → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    HasDerivWithinAt (fun s => g z θ s) (dynLin α g τ z θ + dynRHS α Φ g τ z θ)
      (Set.Icc 0 T) τ

/-- The packaged solution of the dynamic modulated problem *on the interval* `[0,T]`: the elliptic
law holds at every `τ ∈ [0,T]` and the dynamic equation holds within `[0,T]`.  Unlike
`IsDynGSolWith` (a statement for all `τ ≥ 0`, i.e. a solution global in the fake time), this is the
form in which a *local* existence theorem is proved. -/
def IsDynGSolOnT (Law : Fn → Fn → Prop) (α T : ℝ) (Φ g : Fam) : Prop :=
  (∀ τ, 0 ≤ τ → τ ≤ T → Law (Work.Construction.Ftau α g τ) (slice Φ τ)) ∧ IsDynEqOnT α T Φ g

/-- A solution which is global in the fake time restricts to `[0,T]`. -/
theorem IsDynGSolWith.isDynGSolOnT {Law : Fn → Fn → Prop} {α T : ℝ} {Φ g : Fam}
    (h : IsDynGSolWith Law α Φ g) : IsDynGSolOnT Law α T Φ g :=
  ⟨fun τ hτ _ => h.1 τ hτ,
    fun τ hτ _ z θ hz => (h.2 z θ τ hτ hz).mono Set.Icc_subset_Ici_self⟩

/-- **The bundled conclusion of the local well-posedness theorem `lwp_H6` (S1).**

There is a positive time `T`, the datum is attained at `τ = 0`, `(Φ,g)` solves the dynamic
modulated equation with the positivised elliptic law `IsBslSolPos α` *on* `[0,T]`, and `g`
satisfies the `ℋ⁶`-package `RegPkgH6 α T`.

This is a *definition of the conclusion*, not a reduction of S1: the statement of S1 is
`∃ T Φ g, LWPSol α T g₀ Φ g`, and it does not follow from any new axiom introduced here.  A
solution which is global in `τ` (as the existing `Open2`-style chains produce) is converted into
this form by `LWPSol.ofGlobal`. -/
structure LWPSol (α T : ℝ) (g₀ : Fn) (Φ g : Fam) : Prop where
  /-- the time is positive. -/
  pos : 0 < T
  /-- the datum is attained at `τ = 0`. -/
  init : ∀ z θ, g z θ 0 = g₀ z θ
  /-- the dynamic modulated equation with the positivised elliptic law, on `[0,T]`. -/
  sol : IsDynGSolOnT (IsBslSolPos α) α T Φ g
  /-- the `ℋ⁶`-package on `[0,T]`. -/
  h6 : RegPkgH6 α T g

/-- `LWPSol` from a solution which is global in the fake time. -/
theorem LWPSol.ofGlobal {α T : ℝ} {g₀ : Fn} {Φ g : Fam} (hT : 0 < T)
    (hinit : ∀ z θ, g z θ 0 = g₀ z θ) (hsol : IsDynGSolWith (IsBslSolPos α) α Φ g)
    (hh6 : RegPkgH6 α T g) : LWPSol α T g₀ Φ g :=
  ⟨hT, hinit, IsDynGSolWith.isDynGSolOnT hsol, hh6⟩

theorem LWPSol.law {α T : ℝ} {g₀ : Fn} {Φ g : Fam} (h : LWPSol α T g₀ Φ g) :
    ∀ τ, 0 ≤ τ → τ ≤ T → IsBslSolPos α (Work.Construction.Ftau α g τ) (slice Φ τ) := h.sol.1

theorem LWPSol.init' {α T : ℝ} {g₀ : Fn} {Φ g : Fam} (h : LWPSol α T g₀ Φ g) :
    ∀ z θ, g z θ 0 = g₀ z θ := h.init

end Work.FTS.StrongLWP
