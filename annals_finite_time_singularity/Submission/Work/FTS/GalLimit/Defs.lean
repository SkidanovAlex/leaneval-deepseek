/-
# `FTS/GalLimit` — the passage to the limit of the Galerkin scheme (design §3–§4)

This directory owns the *limit vocabulary* of the elliptic/Galerkin design
(`Submission/Work/FTS/FTS_ELL_GALERKIN.md` §3–§4, items 3 and 6–7): the corrected classes on
which the Galerkin span is dense, the corrected elliptic law `IsBslSolPos`, the corrected
formulations of the four passage-to-the-limit inputs (`hPsiLim'`, `hDataLimit'`, `hGalWeak'`,
`hRegLimit'`) and the fundamental lemma of the calculus of variations on the Galerkin span
(`WeakDetermines'`).

## What this file is

`Defs.lean` is a *verbatim* copy — modulo the namespace — of the definitions of the design's
statement file `Submission/Work/FTS/FTS_ELL_GALERKIN_STMTS.lean.txt` that this area owns, with one
addition (`hGalWeak'`, the `Law := IsBslSolPos` form of `DynInputs.hGalWeak`) and one documented
strengthening of the hypothesis list of `weakDetermines'_of` (see `WeakDet.lean`).

The defs are (names as in the design):

| name | role |
|---|---|
| `EBall` | the coefficient ball of radius `r` in `Fin n → ℝ` (the sup-norm ball of `DynInputs` was the wrong shape: it allows `Σc² ≤ 4nR²`); |
| `DenseSpanO` | density of the Galerkin span in `{f : HQo α 4, BdryTraces α 4, L₁₂(f)(0) = 0}` (the *honest* density, replacing the density in `HkAdm`); |
| `CcBasis` | the Galerkin test functions are `C^∞` and compactly supported inside `[a,b] × [δ, π/2−δ]`; |
| `IPLinHQo` | linearity of the concrete `IP4` on the `HQo α 4` class, with its Cauchy–Schwarz constant `Ct`; |
| `IsBslSolPos` | the elliptic law with the Dirichlet conditions imposed only for `z ≥ 0` (the region that `ConvLocUnif` pins); |
| `EqExtra` | the extra regularity needed of `g` and of `RHS(g,Φ)` for the density argument; |
| `WeakDetermines'` | the fundamental lemma for the Galerkin span; |
| `hRegLimit'`, `hDataLimit'`, `hPsiLim'` | the corrected passage-to-the-limit inputs (a further subsequence is allowed in `hPsiLim'`); |
| `hGalWeak'` | the corrected `DynInputs.hGalWeak` with `Law := IsBslSolPos`. |

## Conventions

`Fn = ℝ → ℝ → ℝ` (curried in `(z,θ)`), `Fam = ℝ → ℝ → ℝ → ℝ`.  The open quadrant is
`Work.Construction.Qd = (0,∞) × (0,π/2)`; `Iz = [0,∞)`, `Iθ = [0,π/2]`.  Nothing here is
redefined from `Work.FTS.Vocab`, `Work.FTS.VocabO`, `Work.FTS.VocabO2` or
`Work.FTS.Galerkin.Defs`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.GalerkinFix.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalLimit

open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField IsGalFam ConvLocUnif IsDynWeakOn
  IsDynEqOn RegPkg gdot dynLin dynRHS Slab ProfileBdd ProfileEquicont)
open Work.FTS.Nonlin (GalBasis GalClass UnifIP RegQ CoerAdm PsiCan Xn BdryTraces)
open Work.FTS.VocabO (HQo EllPkgGo)
open Work.FTS.VocabO2 (StarPkgo2)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The coefficient ball -/

/-- The Euclidean ball of radius `r` in `Fin n → ℝ` in the **`ℓ²` form** — the shape the
coercivity of the inner product actually controls (`clo·|f|²₄ ≤ IP(f,f) = Σ cₖ²`), as opposed
to the sup-norm ball `Metric.closedBall 0 R` whose `Σc²` can reach `4nR²`. -/
def EBall (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {c | ∑ k, c k ^ 2 ≤ r ^ 2}

theorem mem_EBall {n : ℕ} {r : ℝ} {c : Fin n → ℝ} : c ∈ EBall n r ↔ ∑ k, c k ^ 2 ≤ r ^ 2 :=
  Iff.rfl

/-! ## The density of the Galerkin span, and the class of the test functions -/

/-- **The density of the Galerkin span in `V₀`** (design §3, item 3): every `f` of the
interior-regular class `HQo α 4` whose integration-by-parts traces vanish (`BdryTraces α 4`) and
whose zero mode vanishes (`L₁₂ f 0 = 0`) is approximated in `|·|_{ℋ⁴}` by a Galerkin combination
`galFun φ c`.  This is the hypothesis of the fundamental lemma (`weakDetermines'_of`), and it is
produced by `exists_galBasis` (design §3). -/
def DenseSpanO (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ f : Fn, HQo α 4 f → BdryTraces α 4 f → Work.Construction.L12 f 0 = 0 → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (c : Fin n → ℝ), Work.Spaces.HkNorm α 4 (fun z θ => f z θ - galFun φ c z θ) < ε

/-- **The class of the Galerkin test functions** (design §3, item 3): every `φ k` is `C^∞` and is
supported in a compact rectangle `[a,b] × [δ, π/2−δ]` strictly inside the closed quadrant.  This is
what makes the tested equations of the Galerkin scheme testable *pointwise* against the limit
(differentiation under the pairings, boundary terms of the `IP`-integrations by parts). -/
def CcBasis (φ : ℕ → Fn) : Prop :=
  ∀ k, ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ δ : ℝ, 0 < δ ∧ ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (φ k)) ∧
    ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → φ k z θ = 0

/-! ## Linearity of the concrete `IP4` on the honest class -/

/-- **Linearity and Cauchy–Schwarz of the concrete `ℋ⁴` inner product on the `HQo α 4` class**
(design §3, item 2).  The class is `HQo α 4 = SmoothOpen ∧ HkMem α 4` — the class closed under the
algebraic operations of the Galerkin scheme, on which the constructive clauses of the concrete
`IP4` hold.

The final clause is the *quadrant congruence*: `IP` only sees the values on the open quadrant. -/
def IPLinHQo (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, HQo α 4 f₁ → HQo α 4 f₂ → HQo α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g ∧
    (∀ c : ℝ, IP α (fun z θ => c * f₁ z θ) g = c * IP α f₁ g) ∧
    |IP α f₁ g| ≤ Ct * Xn α f₁ * Xn α g ∧
    (∀ f', (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f₁ z θ = f' z θ) → IP α f₁ g = IP α f' g)

/-- **Symmetry of `IP` on the honest class.**  Not derivable from `IPLinHQo` (which is a
first-argument statement), but automatic for the concrete `IP4`: every inner product produced by the
induction of the paper's `§Higher order derivatives` is symmetric, and `UnifIP.symm` records that.
It is what turns the tested equations — which give `IP (E) (φ k) = 0` — into `IP E E = 0`. -/
def IPLinHQoSym (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  IPLinHQo IP α₂ Ct ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
    IP α f g = IP α g f

/-- `UnifIP` supplies the symmetry clause (its `symm` field is unrestricted), so in the real chain
the extra hypothesis of `weakDetermines'_of` costs nothing. -/
theorem IPLinHQoSym.of_unifIP {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs Ct : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hL : IPLinHQo IP α₂ Ct) : IPLinHQoSym IP α₂ Ct :=
  ⟨hL, fun α _ f g _ _ => hIP.symm α f g⟩

/-! ## The corrected elliptic law -/

/-- **The elliptic (Biot–Savart) law with the boundary conditions only for `z ≥ 0`.**
`IsBslSolPos α F Ψ` asks `bslOp α Ψ = F` on the open quadrant, the Dirichlet conditions
`Ψ z 0 = Ψ z (π/2) = 0` only for `z ≥ 0`, and the decay `Ψ z θ → 0` as `z → ∞`.

The restriction to `z ≥ 0` is forced by the compactness convergence: `ConvLocUnif` pins the
Galerkin families only on the slab `[0,∞) × [0,π/2] × [0,∞)`, so nothing at all is known about the
elliptic law, or the boundary values, for `z < 0` (`Work.Elliptic.IsBslSol` asks them for all `z`,
which is why it cannot be a limit law — see the integration audit §2). -/
def IsBslSolPos (α : ℝ) (F Ψ : Fn) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
    (∀ z, 0 ≤ z → Ψ z 0 = 0) ∧ (∀ z, 0 ≤ z → Ψ z (π / 2) = 0) ∧
    (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))

theorem isBslSolPos_iff {α : ℝ} {F Ψ : Fn} :
    IsBslSolPos α F Ψ ↔
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
        (∀ z, 0 ≤ z → Ψ z 0 = 0) ∧ (∀ z, 0 ≤ z → Ψ z (π / 2) = 0) ∧
        (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0)) := Iff.rfl

/-- `Work.Elliptic.IsBslSol` implies the positive-`z` law (the equations are the same; only the
range of the boundary conditions is weakened). -/
theorem IsBslSolPos.of_isBslSol {α : ℝ} {F Ψ : Fn} (h : Work.Elliptic.IsBslSol α F Ψ) :
    IsBslSolPos α F Ψ :=
  ⟨h.1, fun z _ => h.2.1 z, fun z _ => h.2.2.1 z, h.2.2.2⟩

theorem IsBslSolPos.bsl {α : ℝ} {F Ψ : Fn} (h : IsBslSolPos α F Ψ) {z : ℝ} (hz : 0 < z)
    {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < π / 2) : Work.Elliptic.bslOp α Ψ z θ = F z θ :=
  h.1 z hz θ hθ hθ'

/-! ## The extra regularity class of the two sides of the equation -/

/-- **The extra regularity of the two sides of the dynamic equation** (design §3).  For every
`τ ≥ 0`: the stream function is smooth on the open quadrant, and both the fake-time derivative
`∂_τg(τ)` and the right hand side `RHS(g,Φ)(τ) = -𝓛_Γ^T g(τ) + gRHS(…)` lie in the admissible class
of the fundamental lemma, i.e. `HQo α 4`, `BdryTraces α 4` and `L₁₂(·)(0) = 0`.

The last two conjuncts are what the *density* argument needs: the test functions used against them
are the algebraically admissible ones, not the whole `ℋ⁴`. -/
def EqExtra (α : ℝ) (g Φ : Fam) : Prop :=
  ∀ τ, 0 ≤ τ → Work.FTS.EllipticEst.SmoothOpen (slice Φ τ) ∧
    HQo α 4 (gdot g τ) ∧ BdryTraces α 4 (gdot g τ) ∧ Work.Construction.L12 (gdot g τ) 0 = 0 ∧
    HQo α 4 (dynLin α g τ + dynRHS α Φ g τ) ∧ BdryTraces α 4 (dynLin α g τ + dynRHS α Φ g τ) ∧
    Work.Construction.L12 (dynLin α g τ + dynRHS α Φ g τ) 0 = 0

/-! ## The fundamental lemma for the Galerkin span -/

/-- **`WeakDetermines'`** (design §4, item 7): the tested (weak) form of the dynamic modulated
equation, for a limit family `g` of the Galerkin scheme with the regularity package `RegPkg` and
the extra regularity `EqExtra`, determines the strong pointwise equation `IsDynEqOn`.

The two extra hypotheses (compared with `Work.FTS.Galerkin.WeakDetermines`) are exactly what the
limit can supply and the Galerkin span needs: `RegPkg α g` makes the `τ`-slices differentiable (so
`deriv = RHS` upgrades to `HasDerivWithinAt`), and `EqExtra` puts both sides of the equation into
the class where the span is dense. -/
def WeakDetermines' (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ g Φ : Fam, RegPkg α g → EqExtra α g Φ → IsDynWeakOn α IP φ g Φ → IsDynEqOn α Φ g

/-! ## The corrected passage-to-the-limit inputs

All four are the fields of the corrected Galerkin bundle in the form the Open3 re-run needs: the
stream functions are allowed to converge only along a *further* subsequence, the regularity package
and the datum are asked only where the compactness convergence pins them, and the elliptic law is
`IsBslSolPos`. -/

/-- **The regularity package and the extra regularity of the limit.**  It replaces
`DynInputs.hRegLimit`: the conclusion is the same but the extra regularity `EqExtra` travels with
it, which is what `hDetermines'` consumes. -/
def hRegLimit' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g Φ : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ →
    ∃ g' : Fam, (∀ p ∈ Slab, g' p.1 p.2.1 p.2.2 = g p.1 p.2.1 p.2.2) ∧ RegPkg α g' ∧
      EqExtra α g' Φ

/-- **The datum is the `τ = 0` slice of the limit, on `Iz × Iθ`.**  It replaces
`DynInputs.hDataLimit`, whose conclusion quantifies over all `z` (including `z < 0`, where the
compactness convergence says nothing); the value `g₀ z θ` on the closed quadrant `z ≥ 0`,
`θ ∈ [0,π/2]` is what `ConvLocUnif` at `τ = 0` pins. -/
def hDataLimit' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (g₀ : Fn) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, g z θ 0 = g₀ z θ

/-- **The stream functions have a locally uniform limit, along a further subsequence.**  It
replaces `DynInputs.hPsiLim`, which demanded the limit along the *same* subsequence as the profiles:
since the stream functions are `Φ_* + EllSol(·)` and only the coefficients of the Galerkin family
are pinned by the profile convergence, a further extraction is unavoidable, and it costs nothing
downstream. -/
def hPsiLim' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ∃ (ψ' : ℕ → ℕ) (Φ : Fam), StrictMono ψ' ∧
      ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ (ψ' n)) (c (ψ (ψ' n))))) Φ

/-- **The tested equations and the elliptic law pass to the limit** (the corrected
`DynInputs.hGalWeak`, with `Law := IsBslSolPos α`).  The scalar tested equations give the limit's
weak form; the Galerkin elliptic identities `bslOp α (EllSol gₙ(τ)) = gₙ(τ)` pass to
`IsBslSolPos α (F_* + g(τ)) (Φ(τ))`. -/
def hGalWeak' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g Φ : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ →
    IsDynWeakOn α (IP α) φ g Φ ∧
      (∀ τ : ℝ, 0 ≤ τ → IsBslSolPos α (Work.Construction.Ftau α g τ) (slice Φ τ))

/-- The Lipschitz form of the field bound, on the `ℓ²`-ball `EBall n (2R)`. -/
def hField_lip' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
    LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ) (EBall n (2 * R))

end Work.FTS.GalLimit
