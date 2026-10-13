/-
# `Submission/Work/FTS/OpenPkg/` — the open-quadrant (interior) migration of the nonlinear,
# a-priori and Galerkin interfaces

## Why this chapter exists

The frozen packages `Work.FTS.Nonlin.EllPkgG` and `Work.FTS.Nonlin.StarPkg`
(`Submission/Work/FTS/Vocab.lean`) are **uninhabited by the real stream functions** of the route:

* `StarPkg.smooth` / `EllPkgG.smooth` ask for `Work.FTS.LocData.SmoothQuad`, i.e. `C^∞` *through*
  `z = 0`; every decaying solution of `bslOp α Φ = F` carries the homogeneous modes
  `z^{2m/α}` (or `z^{2m/α} log z`), so it is only `C^{⌊2/α⌋}` at `z = 0`;
* `RegQ` contains `BdryTraces`, which forces vanishing at `θ = 0, π/2` of the coefficients
  `ℛ(Φ̃)`, `U(Φ̃)/sin 2θ` and `V(Φ̃)`, which do not vanish there.

`Work.FTS.VocabO` (lead-frozen, 2026-10-04) supplies the replacements
`EllPkgGo`, `StarPkgo`, `HQo`, `WDp`, `WDMem`, `CoefTh`, `CoefThMem`, `T2Clause`, `T3Clause`.
This chapter is the *migration* of every consumer of the frozen packages to the open-quadrant
ones: the primed interfaces, their basic API, the assembly `pairing_bound'`, the a-priori
chapter (N5) and the Galerkin existence chapter (N6) under the new hypotheses, and the wiring of
the top-level (N0) assembly.

## What is in this file

The vocabulary of the migration (nothing here is a proof obligation by itself; the inhabitation
lemmas are in the sibling modules):

* `N4Norm'` — the norm-level facts of the N3-fix node, in the open-quadrant class (`HQo`,
  `WDp`/`WDMem` replacing `RegQ`, `WlInf`/`WlInfMem`, `SmoothQuad`/`SmoothInt` replacing nothing);
* `N4Extra'` — the `IP`-level transport contract for the concrete `IP₄`, with the honesty
  hypothesis `Work.Spaces.HkMem α 4 f` on the first argument of **every** clause (for
  `f ∉ ℋ⁴` the norm `Xn α f` is the junk value `0` while the pairing can be honest, so the
  un-primed clauses are *not* jointly satisfiable with `UnifIP`; see `FTS/ELL_H2_LEAD.md` §B3),
  and with the transport clauses `t2`/`t3` replaced by `VocabO.T2Clause`/`VocabO.T3Clause`
  (a flat angular coefficient `CoefTh` and order-5 honesty of `g`);
* `RowCtx'` and `RowInputs'` — the context and the per-piece table of the §8 estimates in the
  primed vocabulary, ready for `FTS/NonlinRows` to inhabit (each row gains the `ℋ⁴`-honesty
  conjunct of its own piece, which is what `N4Extra'`'s clauses consume);
* `N4Rows'` (`rowsN0Open`/`rowsNOpen`/`rowsAuxOpen` bundled) — the row groups as an interface;
* `PairData'` — the output of `pairing_bound'` with `StarPkgo`/`EllPkgGo`;
* `LimBoundOpen`, `GalEnergyIneq`, `AprioriFields'` — the a-priori (N5) chapter's interface, with
  the `SmoothQuad` requirement on the limit profile's slices replaced by `SmoothOpen`;
* `DynCore`, `DynInputsOpen` — the Galerkin (N6) bundle with the o-packages and the open-quadrant
  limit bound, and the projection onto the part of the bundle that the ODE/existence layer uses;
* `OpenChapter` — the bundle of all the mathematical inputs of the migrated route, i.e. the exact
  hypothesis list of the top-level (N0) assembly.

## Conventions

`Fn = ℝ → ℝ → ℝ` (curried `f z θ`), `Fam = ℝ → ℝ → ℝ → ℝ` (`g z θ τ`), integrals over
`[0,∞) × [0,π/2]` with the measure `dz dθ`.  `Xn α g = Work.Spaces.HkNorm α 4 g`.  All constants
are absolute (independent of `α`, of the profiles and of the truncation).
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Nonlinear.RowInputs
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Apriori.Defs
import Submission.Work.FTS.GalerkinFix.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField coeffOf IsSolOn IsGalFam
  ConvLocUnif muDyn lamDyn dynLin dynRHS DenseSpan WeakDetermines IsDynWeakOn ProfileBdd
  EquicontSpace EquicontTau profileFam RegPkg prof Slab)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The norm-level interface in the open-quadrant class -/

/-- **The primed norm interface** (`FTS/ELL_H2_LEAD.md` §B1 "Downstream edits").

The fields are those of `Work.FTS.Nonlin.N4Norm`, with

* `RegQ` replaced by `VocabO.HQo` (interior `C^∞` + honesty; **no** `BdryTraces`);
* `Work.FTS.LocData.SmoothQuad` / `Work.Spaces.SmoothInt` replaced by
  `Work.FTS.EllipticEst.SmoothOpen`;
* `Work.Spaces.WlInf`/`WlInfMem` replaced by `VocabO.WDp`/`WDMem` (`WlInf` demands true
  `(z+1)^k ∂_z^k` suprema up to `z = 0`, which the remainder of the `Φ_*` decomposition does not
  have; `WDp ≤ C_l · WlInf` on the smooth class, so nothing is lost).

Every field is a true statement about the paper's function spaces; the inhabitation lemmas are in
`Submission/Work/FTS/OpenPkg/NormFields/`. -/
structure N4Norm' (Ci α₂ : ℝ) : Prop where
  pos : 0 < Ci ∧ 0 < α₂
  /-- `ℋ⁴` is closed under products, with the loss `√10 α^{-1/2}` (`HProdQ`, tex 1086). -/
  prod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Xn α (fun z θ => f z θ * g z θ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g
  /-- Multiplication by a `𝒲^{4,∞}`-function (`WProdQ`, tex 1096).

  **This clause must be priced by the `𝒲`-norm, not by `WDp`.**  Independent refutations
  (`Work.FTS.OpenPkg.wprod_field`, declared false by its prover, and the review of
  `Work.FTS.OpenPkg.wtoh_field`) show that a `D`-sup bound on the coefficient is *not* enough: a
  coefficient which is `C^∞` on the open quadrant, has bounded `D`-derivatives, but whose angular
  derivatives do not decay at `θ = 0, π/2` (`f z θ = sin (log (1/θ))`, or the spike family
  `f_s = (z²/(1+z)³)·sin(2θ)^s` with `s ↓ (γ-1)/2`) violates the conclusion: the mixed slots of
  the product are weighted by `sin(2θ)^{-γ}` with `γ = 1 + α/10 > 1`, so the `ℋ⁴`-integral sees
  the angular decay while the plain `D`-sup does not.  The `𝒲^{4,∞}`-norm of the coefficient is
  exactly the missing information (its weight `sin(2θ)^{-α/5}/(α+sin 2θ)` is comparable to
  `sin(2θ)^{-γ}` in the slots with `j ≥ 1`).

  For the rows this is also the only usable form for coefficients which are not in `ℋ⁴`
  (`F_*`, `D_θF_*`, `D_zF_*`: the `i = 4` angular slot of `F_*` is not integrable). -/
  wprod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.WlInfMem α 4 f → HQo α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Xn α (fun z θ => f z θ * g z θ)
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g
  /-- `𝒲^{4,∞}` controls `ℋ⁴` through the weight `(z+1)³/z²` (`WtoHQ`, tex 1160).

  As for `wprod`, the hypothesis must be the `𝒲`-membership of the *weighted* function: the
  `D`-sup form is refuted (review of `Work.FTS.OpenPkg.wtoh_field`; spike family
  `f_s = (z²/(1+z)³)ψ(z)·sin(2θ)^s` has `WDp 4 ((z+1)³/z²·f_s) = O(1)` while `Xn α f_s → ∞`). -/
  wtoh : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) →
    Xn α f ≤ Ci * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
  /-- `L₁₂` maps the `ℋ⁴`-class into itself, losslessly (`L12HQ`, tex 1119). -/
  l12H : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → Work.Construction.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
    Xn α (fun z θ => Work.Construction.L12 g z) ≤ Ci * Xn α g
  /-- The zero mode of `L₁₂` is controlled by the `ℋ⁴`-norm (`L12ZeroQ`, tex 1519). -/
  l12zero : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, HQo α 4 f →
    |Work.Construction.L12 f 0| ≤ Ci * Xn α f
  /-- The angular moment `FK g = ∫_θ K(θ) g(z,θ) dθ` is an `ℋ⁴`-function controlled by `Xn α g`. -/
  fkH : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → Work.Construction.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
    Xn α (fun z _ => Work.Construction.FK g z) ≤ Ci * Xn α g
  /-- `z ↦ L₁₂(g)(z)` is differentiable on `(0,∞)` in the interior class. -/
  l12diff : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → ∀ z ∈ Set.Ioi (0 : ℝ),
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z
  /-- Multiplication by a function of `z` alone is lossless in `α` (`radial_prod`). -/
  radialMul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (r : ℝ → ℝ) (g : Fn),
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α 4 (fun z _ => r z) → Work.Spaces.HkMem α 4 g →
    (∀ b : ℕ, b ≤ 4 → Filter.Tendsto
      (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => r z) z 0) Filter.atTop (nhds 0)) →
    (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
    Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
    Xn α (fun z θ => r z * g z θ) ≤ Ci * Xn α (fun z _ => r z) * Xn α g
  /-- Multiplication by an angular profile is lossless in `α`
  (`HkIntegrand_mul_angular_le`).  `a` must be bounded and its `D_θ`-iterates must vanish at
  least like `sin(2θ)`. -/
  angmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (f : Fn),
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
    (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
    Xn α (fun z θ => a θ * f z θ) ≤ Ci * Ci * Xn α f
  /-- Multiplication by an angular profile in the `D`-sup norm. -/
  wang : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (h : Fn),
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
    Work.FTS.EllipticEst.SmoothOpen h →
    (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
    WDMem 4 h →
    WDMem 4 (fun z θ => a θ * h z θ) ∧
    WDp 4 (fun z θ => a θ * h z θ) ≤ Ci * Ci * WDp 4 h
  /-- Multiplication by a `z`-profile in the `D`-sup norm. -/
  wrad : ∀ α ∈ Set.Ioc 0 α₂, ∀ (φ : ℝ → ℝ) (h : Fn),
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => φ z) →
    Work.FTS.EllipticEst.SmoothOpen h →
    WDMem 4 (fun z _ => φ z) → WDMem 4 h →
    WDMem 4 (fun z θ => φ z * h z θ) ∧
    WDp 4 (fun z θ => φ z * h z θ) ≤ Ci * WDp 4 (fun z _ => φ z) * WDp 4 h
  /-- **The `D`-sup product rule**, with the flat vanishing of one factor on the two angular
  boundary lines which makes the boundary values of `pzIter k` harmless. -/
  wmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
    WDMem 4 f → WDMem 4 g →
    (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ,
      Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) →
    WDMem 4 (fun z θ => f z θ * g z θ) ∧
    WDp 4 (fun z θ => f z θ * g z θ) ≤ Ci * WDp 4 f * WDp 4 g

/-! ## The `IP`-level contract in the open-quadrant class -/

/-- **The primed `IP`-level facts consumed by N4.**

`IP` is the paper's concrete `ℋ⁴` inner product (`IP₄`).  Compared with
`Work.FTS.Nonlin.N4Extra`:

* **every clause carries the honesty hypothesis `HkMem α 4 f` on the first argument(s) it
  quantifies over** (and `SmoothOpen f` where the proof needs differentiability of `f`).  This is
  what makes the structure *jointly satisfiable with `UnifIP`*: for `f ∉ ℋ⁴` the norm `Xn α f` is
  the junk value `0` while `IP α f g` can be an honest non-zero number, so the un-primed clauses
  `cs`, `add`, `smul`, `neg`, `congr`, `t1`, `t4`, `st` are false for the concrete `IP₄`
  (`FTS/ELL_H2_LEAD.md` §B3, "faithfulness defect of the current `N4Extra`");
* the transport clauses `t2`/`t3` are *replaced* by `VocabO.T2Clause`/`VocabO.T3Clause`: the
  angular liveness of the coefficient is measured by the flat norm `CoefTh` (so that a spike
  family is excluded by hypothesis rather than by a false bound) and the `g`-side carries order-5
  honesty, which removes the `z`-outer junk-integral obstruction;
* the `𝒲^{4,∞}`-clauses `t3`/`t4`/`st` are stated in `WDp`/`WDMem`.

`satisfiable` is *not* asserted here: the inhabitation for the concrete `IP₄` is the row side's
obligation (`FTS/NonlinRows`); this structure is the contract. -/
structure N4Extra' (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop where
  pos : 0 < Ct ∧ 0 < α₂
  /-- Cauchy–Schwarz against the `ℋ⁴`-norm, on honest first arguments. -/
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.HkMem α 4 f → RegQ α 4 g →
    |IP α f g| ≤ Ct * Xn α f * Xn α g
  /-- Additivity in the first argument. -/
  add : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, Work.Spaces.HkMem α 4 f₁ →
    Work.Spaces.HkMem α 4 f₂ → RegQ α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  /-- Homogeneity in the first argument. -/
  smul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ) (f g : Fn), Work.Spaces.HkMem α 4 f → RegQ α 4 g →
    IP α (fun z θ => c * f z θ) g = c * IP α f g
  /-- Negation in the first argument. -/
  neg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.HkMem α 4 f → RegQ α 4 g →
    IP α (fun z θ => -f z θ) g = -IP α f g
  /-- `IP` only depends on the first argument through its values on the open quadrant `Qd`. -/
  congr : ∀ α ∈ Set.Ioc 0 α₂, ∀ f f' g : Fn, Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 4 f' → RegQ α 4 g →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP α f g = IP α f' g
  /-- The `D_z`-self-pairing, lossless (design §5 T5). -/
  dz : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → |IP α (Work.Spaces.Dz g) g| ≤ Ct * Xn α g ^ 2
  /-- `T1Q`: transport with `D_θ` and an `ℋ⁴`-coefficient (tex 1119). -/
  t1 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2
  /-- `T2S`: transport with `D_z` and a flat angular coefficient (`VocabO.T2Clause`). -/
  t2 : T2Clause IP α₂ Ct
  /-- `T3S`: transport with `D_z` and a `𝒲^{4,∞}`-coefficient (`VocabO.T3Clause`). -/
  t3 : T3Clause IP α₂ Ct
  /-- `T3Q` with `D_θ` and a `𝒲^{4,∞}`-coefficient, in the `D`-sup norm. -/
  t4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, WDMem 4 f → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * WDp 4 f * Xn α g ^ 2
  /-- `STQ`: `SpecialTransport` (tex 1258), the derivative falling on a coefficient which
  vanishes at the angular ends. -/
  st : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.VanishTheta f →
    WDMem 4 (Work.Spaces.pth f) → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.pth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * WDp 4 (Work.Spaces.pth f) * Xn α g ^ 2

/-! ## The per-piece rows of the §8 estimate in the primed vocabulary -/

/-- **The context of the per-piece estimates** (the primed `Work.FTS.Nonlin.RowCtx`): the two
primed interfaces, the two open-quadrant elliptic packages, the Galerkin class of the
perturbation and the ranges of `α`. -/
structure RowCtx' (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs α : ℝ) (g Φs Φg : Fn) : Prop where
  hCi : 0 < Ci
  hN : N4Norm' Ci α₂
  hE : N4Extra' IP α₂ Ct
  hα : 0 < α
  hαα₂ : α ≤ α₂
  hα1 : α ≤ 1
  hg : GalClass α g
  hs : StarPkgo α Cs Φs
  hell : EllPkgGo α Ce g Φg

variable {IP : ℝ → Fn → Fn → ℝ} {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn}

theorem RowCtx'.reg4 (h : RowCtx' IP α₂ Ci Ct Ce Cs α g Φs Φg) : RegQ α 4 g :=
  Work.FTS.Nonlin.galClass_regQ4 h.hg

theorem RowCtx'.hαIoc (h : RowCtx' IP α₂ Ci Ct Ce Cs α g Φs Φg) : α ∈ Set.Ioc 0 α₂ :=
  ⟨h.hα, h.hαα₂⟩

theorem RowCtx'.hregQ (h : RowCtx' IP α₂ Ci Ct Ce Cs α g Φs Φg) : 0 < α₂ := h.hN.pos.2

/-- **The per-piece table of §8 in the primed vocabulary.**

The fields are those of `Work.FTS.Nonlin.RowInputs` — the concrete inequalities of design §3.4 —
**with the `ℋ⁴`-honesty conjunct of the piece added to every norm bound**.  That conjunct is
exactly what `N4Extra'`'s clauses consume (they take `HkMem α 4 f` as a hypothesis), and it is
what the row proofs produce anyway (`HProdQ`, `L12HQ`, `WtoHQ`, … all conclude
`HkMem α 4 (piece) ∧ bound`).

The four fields `hkN0`, `hkN`, `hkAK`, `hkDz` are the honesty of the three blocks into which
`gRHS` is split, plus that of `D_z g`; they are the ones the *assembly* (`pairing_bound'`) needs in
addition to the per-piece rows. -/
structure RowInputs' (IP : ℝ → Fn → Fn → ℝ) (α C : ℝ) (g Φs Φg : Fn) : Prop where
  reg4 : RegQ α 4 g
  /-- row 1: `|N₀₁+N₀₂|_{ℋ⁴} ≤ Cα²` -/
  r1 : Work.Spaces.HkMem α 4 (N0fix α) ∧ Xn α (N0fix α) ≤ C * α ^ 2
  /-- row 2: `|N₀₃|_{ℋ⁴} ≤ Cα^{-1}X²` -/
  r2 : Work.Spaces.HkMem α 4 (N03g α g) ∧
    Xn α (N03g α g) ≤ C * (α ^ (-(1 : ℝ)) * Xn α g ^ 2)
  /-- row 3: `|N₀₄ᵃ|_{ℋ⁴} ≤ C√α X` -/
  r3 : Work.Spaces.HkMem α 4 (N04aF α g) ∧
    Xn α (N04aF α g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 4: `|(N₀₄ᵇ, g)| ≤ Cα^{-3/2}X³` -/
  r4 : Work.Spaces.HkMem α 4 (N04bF α g) ∧
    |IP α (N04bF α g) g| ≤ C * (α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 5: `|N₀₅ᵃ|_{ℋ⁴} ≤ C√α X` -/
  r5 : Work.Spaces.HkMem α 4 (N05aF α g) ∧
    Xn α (N05aF α g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 6: `|(N₀₅ᵇ, g)| ≤ Cα^{-1/2}X³` -/
  r6 : Work.Spaces.HkMem α 4 (N05bF α g) ∧
    |IP α (N05bF α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 7: `|(N₀₆, g)| ≤ C√α X²` -/
  r7 : Work.Spaces.HkMem α 4 (N06F α g) ∧
    |IP α (N06F α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r8 : Work.Spaces.HkMem α 4 (N1gg α g Φg) ∧
    Xn α (N1gg α g Φg) ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 2)
  r9 : Work.Spaces.HkMem α 4 (N1gs α g Φg) ∧
    Xn α (N1gs α g Φg) ≤ C * (Real.sqrt α * Xn α g)
  r10 : Work.Spaces.HkMem α 4 (N1sg α Φs g) ∧
    Xn α (N1sg α Φs g) ≤ C * (Real.sqrt α * Xn α g)
  r11 : Work.Spaces.HkMem α 4 (N1ss α Φs) ∧ Xn α (N1ss α Φs) ≤ C * α ^ 2
  r12 : Work.Spaces.HkMem α 4 (N2gg α g Φg) ∧
    |IP α (N2gg α g Φg) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r13 : Work.Spaces.HkMem α 4 (N2gs α g Φg) ∧
    Xn α (N2gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r14 : Work.Spaces.HkMem α 4 (N2sg α Φs g) ∧
    |IP α (N2sg α Φs g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r15 : Work.Spaces.HkMem α 4 (N2ss α Φs) ∧ Xn α (N2ss α Φs) ≤ C * α ^ 2
  r16 : Work.Spaces.HkMem α 4 (N3gg α g Φg) ∧
    |IP α (N3gg α g Φg) g| ≤ C * (Real.sqrt α * Xn α g ^ 3)
  r17 : Work.Spaces.HkMem α 4 (N3gs α g Φg) ∧
    Xn α (N3gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r18 : Work.Spaces.HkMem α 4 (N3sg α Φs g) ∧
    |IP α (N3sg α Φs g) g| ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g ^ 2)
  r19 : Work.Spaces.HkMem α 4 (N3ss α Φs) ∧ Xn α (N3ss α Φs) ≤ C * α ^ 3
  r20 : Work.Spaces.HkMem α 4 (N4gg α g) ∧
    |IP α (N4gg α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r21 : Work.Spaces.HkMem α 4 (N4gs α g) ∧
    Xn α (N4gs α g) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r22 : Work.Spaces.HkMem α 4 (N4sg α g) ∧
    |IP α (N4sg α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r23 : Work.Spaces.HkMem α 4 (N4ss α) ∧ Xn α (N4ss α) ≤ C * α ^ 3
  r24 : Work.Spaces.HkMem α 4 (N5gg g) ∧ Xn α (N5gg g) ≤ C * Xn α g ^ 2
  r25 : Work.Spaces.HkMem α 4 (N5gs α g) ∧ Work.Spaces.HkMem α 4 (N5sg α g) ∧
    Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * Xn α g)
  r26 : Work.Spaces.HkMem α 4 (N5ss α) ∧ Xn α (N5ss α) ≤ C * α ^ 2
  /-- the `ℋ⁴`-bound of `AK` (design §3.2) -/
  rak : Work.Spaces.HkMem α 4 (Work.Construction.AK α) ∧ Xn α (Work.Construction.AK α) ≤ C
  rl0 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl1 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ C * Xn α g
  hN0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
      = N0fix α z θ + (N03g α g z θ + N04aF α g z θ + N04bF α g z θ
          + N05aF α g z θ + N05bF α g z θ + N06F α g z θ)
  hN : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      = (N1gg α g Φg z θ + N1gs α g Φg z θ + N1sg α Φs g z θ + N1ss α Φs z θ)
        + (N2gg α g Φg z θ + N2gs α g Φg z θ + N2sg α Φs g z θ + N2ss α Φs z θ)
        + (N3gg α g Φg z θ + N3gs α g Φg z θ + N3sg α Φs g z θ + N3ss α Φs z θ)
        + (N4gg α g z θ + N4gs α g z θ + N4sg α g z θ + N4ss α z θ)
        + (N5gg g z θ + N5gs α g z θ + N5sg α g z θ + N5ss α z θ)
  hNs : ∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = NstarLam μ g z θ
  /-- honesty of the `N₀`-block (`N0 α (F_*+g) g`) -/
  hkN0 : Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
  /-- honesty of the `N`-block (`N α (F_*+g) (Φ_*+Φ_g)`) -/
  hkN : Work.Spaces.HkMem α 4
    (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
  /-- honesty of `D_z g` -/
  hkDz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g)

/-! ## The row groups as an interface -/

/-- **The `ℋ⁴`-honesty of every piece entering the assembly of `pairing_bound'`.**  These are the
hypotheses that the primed clauses of `N4Extra'` consume; each is produced by the row proof of the
corresponding piece. -/
structure PiecesHk (α : ℝ) (g Φs Φg : Fn) : Prop where
  p1 : Work.Spaces.HkMem α 4 (N0fix α)
  p2 : Work.Spaces.HkMem α 4 (N03g α g)
  p3 : Work.Spaces.HkMem α 4 (N04aF α g)
  p4 : Work.Spaces.HkMem α 4 (N04bF α g)
  p5 : Work.Spaces.HkMem α 4 (N05aF α g)
  p6 : Work.Spaces.HkMem α 4 (N05bF α g)
  p7 : Work.Spaces.HkMem α 4 (N06F α g)
  p8 : Work.Spaces.HkMem α 4 (N1gg α g Φg)
  p9 : Work.Spaces.HkMem α 4 (N1gs α g Φg)
  p10 : Work.Spaces.HkMem α 4 (N1sg α Φs g)
  p11 : Work.Spaces.HkMem α 4 (N1ss α Φs)
  p12 : Work.Spaces.HkMem α 4 (N2gg α g Φg)
  p13 : Work.Spaces.HkMem α 4 (N2gs α g Φg)
  p14 : Work.Spaces.HkMem α 4 (N2sg α Φs g)
  p15 : Work.Spaces.HkMem α 4 (N2ss α Φs)
  p16 : Work.Spaces.HkMem α 4 (N3gg α g Φg)
  p17 : Work.Spaces.HkMem α 4 (N3gs α g Φg)
  p18 : Work.Spaces.HkMem α 4 (N3sg α Φs g)
  p19 : Work.Spaces.HkMem α 4 (N3ss α Φs)
  p20 : Work.Spaces.HkMem α 4 (N4gg α g)
  p21 : Work.Spaces.HkMem α 4 (N4gs α g)
  p22 : Work.Spaces.HkMem α 4 (N4sg α g)
  p23 : Work.Spaces.HkMem α 4 (N4ss α)
  p24 : Work.Spaces.HkMem α 4 (N5gg g)
  p25 : Work.Spaces.HkMem α 4 (N5gs α g)
  p26 : Work.Spaces.HkMem α 4 (N5sg α g)
  p27 : Work.Spaces.HkMem α 4 (N5ss α)
  pAK : Work.Spaces.HkMem α 4 (Work.Construction.AK α)
  pN0 : Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
  pN : Work.Spaces.HkMem α 4
    (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
  pDz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g)

/-! ## The row groups as an interface -/

/-- **The three row groups of design §3.4, in the primed context**, bundled with the two exact
splits and the `N_*`-collapse of `RowInputs'`.

This is the *statement* that `FTS/NonlinRows` inhabits (rows 6, 7, 16, 18 consume
`VocabO.T2Clause`/`T3Clause`; rows 10, 11, 14, 15, 18, 19 consume `StarPkgo`); the assembly
`pairing_bound'` below is proved from it. -/
structure N4Rows' (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) where
  K₁ : ℝ
  K₂ : ℝ
  K₃ : ℝ
  hK₁ : 0 < K₁
  hK₂ : 0 < K₂
  hK₃ : 0 < K₃
  /-- rows 1--7 -/
  rowsN0 : ∀ {α : ℝ} {g Φs Φg : Fn}, 0 < α → α ≤ 1 → α ≤ α₂ → GalClass α g →
    StarPkgo α Cs Φs → EllPkgGo α Ce g Φg →
    Work.FTS.Nonlinear.Pieces.N0Rows IP α K₁ g Φs Φg
  /-- rows 8--26 -/
  rowsN : ∀ {α : ℝ} {g Φs Φg : Fn}, 0 < α → α ≤ 1 → α ≤ α₂ → GalClass α g →
    StarPkgo α Cs Φs → EllPkgGo α Ce g Φg →
    Work.FTS.Nonlinear.Pieces.NRows IP α K₂ g Φs Φg
  /-- the auxiliary rows (`AK` and the three zero modes) -/
  rowsAux : ∀ {α : ℝ} {g Φs Φg : Fn}, 0 < α → α ≤ 1 → α ≤ α₂ → GalClass α g →
    StarPkgo α Cs Φs → EllPkgGo α Ce g Φg →
    Work.FTS.Nonlinear.Pieces.AuxRows IP α K₃ g Φs Φg
  /-- the three exact splits of `N₀`, `N` and `N_*` -/
  splits : ∀ {α : ℝ} {g Φs Φg : Fn}, 0 < α → α ≤ 1 → α ≤ α₂ → GalClass α g →
    StarPkgo α Cs Φs → EllPkgGo α Ce g Φg →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
        = N0fix α z θ + (N03g α g z θ + N04aF α g z θ + N04bF α g z θ
            + N05aF α g z θ + N05bF α g z θ + N06F α g z θ)) ∧
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
        = (N1gg α g Φg z θ + N1gs α g Φg z θ + N1sg α Φs g z θ + N1ss α Φs z θ)
          + (N2gg α g Φg z θ + N2gs α g Φg z θ + N2sg α Φs g z θ + N2ss α Φs z θ)
          + (N3gg α g Φg z θ + N3gs α g Φg z θ + N3sg α Φs g z θ + N3ss α Φs z θ)
          + (N4gg α g z θ + N4gs α g z θ + N4sg α g z θ + N4ss α z θ)
          + (N5gg g z θ + N5gs α g z θ + N5sg α g z θ + N5ss α z θ)) ∧
    (∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
      Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = NstarLam μ g z θ)
  /-- the honesty conjuncts of the pieces (`FTS/NonlinRows` produces them together with the rows) -/
  hkmem : ∀ {α : ℝ} {g Φs Φg : Fn}, 0 < α → α ≤ 1 → α ≤ α₂ → GalClass α g →
    StarPkgo α Cs Φs → EllPkgGo α Ce g Φg → PiecesHk α g Φs Φg

/-! ## The output of the primed pairing estimate -/

/-- **The output of `pairing_bound'`**, with `StarPkgo`/`EllPkgGo` (the primed analogue of
`Work.FTS.Apriori.PairData`). -/
structure PairData' (IP : ℝ → Fn → Fn → ℝ) (CcN Ce Cs α₄ : ℝ) : Prop where
  hCcN : 0 < CcN
  hα₄ : 0 < α₄
  bound : ∀ α : ℝ, 0 < α → α ≤ α₄ → ∀ g Φs Φg : Fn,
    GalClass α g → StarPkgo α Cs Φs → EllPkgGo α Ce g Φg → Xn α g ≤ α ^ (7 / 4 : ℝ) →
    |Work.FTS.Apriori.muOf α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * (α + α ^ (-(1 : ℝ)) * Xn α g + α ^ (-(5 / 2 : ℝ)) * Xn α g ^ 2)
      ∧ |Work.FTS.Apriori.muOf α g (fun z θ => Φs z θ + Φg z θ)| ≤ 1 / 2
      ∧ |Work.FTS.Apriori.rhsPair IP α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * Pbd α (Xn α g)

/-! ## The a-priori (N5) interface, open-quadrant form -/

/-- **The a-priori fields of N6, in the primed vocabulary.**  Field for field those of
`Work.FTS.Apriori.AprioriFields`, with the primed packages and the open-quadrant limit bound. -/
structure AprioriFields' (IP : ℝ → Fn → Fn → ℝ) (α C₀ clo cc CcN Ce Cs : ℝ) (φ : ℕ → Fn)
    (Φs : Fn) (EllSol : Fn → Fn) (g₀ : Fn) : Prop where
  /-- **`hInit`**: the projected datum lies in the a-priori ball. -/
  hInit : ∀ n : ℕ, ∑ k : Fin n,
    (coeffOf (IP α) g₀ φ n k) ^ 2 ≤ (Work.FTS.Apriori.Rstar clo C₀ α) ^ 2
  /-- **`hCoeffBound`**: every Galerkin solution stays in the a-priori ball. -/
  hCoeffBound : ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
    IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, ∑ k : Fin n, (c τ k) ^ 2 ≤ (Work.FTS.Apriori.Rstar clo C₀ α) ^ 2
  /-- **`hProfileBdd`**: uniform local bounds on the Galerkin profiles. -/
  hProfileBdd : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Work.FTS.Apriori.Rstar clo C₀ α) c →
    ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.Galerkin.Slab →
      ∃ Cb : ℝ, ∀ n : ℕ, ∀ p ∈ K, |Work.FTS.Galerkin.prof φ c n p| ≤ Cb
  /-- **`hLimBound`**: the limit of a convergent subsequence obeys the a-priori bound.  The
  slices of the limit are required to be `SmoothOpen` — which `RegPkg.smooth` supplies — not
  `SmoothQuad`. -/
  hLimBound : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Work.FTS.Apriori.Rstar clo C₀ α) c →
    ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    (∀ τ : ℝ, 0 ≤ τ → Work.FTS.EllipticEst.SmoothOpen (slice g τ)) →
    ∀ τ : ℝ, 0 ≤ τ → Xn α (slice g τ) ≤ C₀ * α ^ 2

/-! ## The Galerkin (N6) bundle, open-quadrant form -/

/-- **The part of the Galerkin a-priori bundle that the ODE/existence layer uses.**

This is the projection of `Work.FTS.Galerkin.DynInputs` onto the fields that are actually consumed
by `galerkin_coeff_exists` and `exists_dynGSol_of_ode`: the inner product and its constants, the
basis and its density, the two stream functions (as *data* — their packages are **not** part of
this structure), the a-priori radius, the field constants, the compactness/limit inputs and the
limit bound.

Separating it is what allows the migration: the frozen packages `StarPkg`/`EllPkgG` occur only in
the three fields of `DynInputs` that this structure drops (`hΦs`, `hEllSol` and their constants). -/
structure DynCore (Law : Fn → Fn → Prop) (α : ℝ) (g₀ : Fn) (C₀ : ℝ) where
  IP : ℝ → Fn → Fn → ℝ
  α₂ : ℝ
  cc : ℝ
  clo : ℝ
  Cup : ℝ
  Ccs : ℝ
  hIP : UnifIP IP α₂ cc clo Cup Ccs
  φ : ℕ → Fn
  hφ : GalBasis α IP φ
  hφ_dense : DenseSpan α IP φ
  Φs : Fn
  EllSol : Fn → Fn
  hPsi : ∀ G : Fam, (∀ τ : ℝ, 0 ≤ τ → GalClass α (slice G τ)) → ∀ τ : ℝ, 0 ≤ τ →
    Law (Work.Construction.Ftau α G τ) (slice (PsiCan Φs EllSol G) τ)
  R : ℝ
  hR : 0 < R
  L : ℕ → ℝ
  hL : ∀ n : ℕ, 0 < L n
  K : ℕ → ℝ
  hK : ∀ n : ℕ, 0 ≤ K n
  hField_lip : ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
    LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ)
      (Metric.closedBall 0 (2 * R))
  hField_bound : ∀ (n : ℕ) (τ : ℝ) (c : Fin n → ℝ), 0 ≤ τ →
    c ∈ Metric.closedBall 0 (2 * R) → ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n
  hField_cont : ∀ (n : ℕ) (c : Fin n → ℝ), c ∈ Metric.closedBall 0 (2 * R) →
    ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0)
  hInit : ∀ n : ℕ, ∑ k : Fin n, (coeffOf (IP α) g₀ φ n k) ^ 2 ≤ R ^ 2
  hCoeffBound : ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
    IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, ∑ k : Fin n, (c τ k) ^ 2 ≤ R ^ 2
  hProfileBdd : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    ProfileBdd (profileFam φ c)
  hProfileSpace : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    EquicontSpace (profileFam φ c)
  hProfileTau : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    EquicontTau (profileFam φ c)
  hRegLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → RegPkg α g
  hDataLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → ∀ z θ, g z θ 0 = g₀ z θ
  hPsiLim : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ∃ Φ : Fam, ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ
  hGalWeak : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g Φ : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ →
    IsDynWeakOn α (IP α) φ g Φ ∧ (∀ τ : ℝ, 0 ≤ τ → Law (Work.Construction.Ftau α g τ) (slice Φ τ))
  hDetermines : WeakDetermines α (IP α) φ
  hLimBound : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    (∀ τ : ℝ, 0 ≤ τ → Work.FTS.EllipticEst.SmoothOpen (slice g τ)) →
    ∀ τ : ℝ, 0 ≤ τ → Work.Spaces.HkNorm α 4 (slice g τ) ≤ C₀ * α ^ 2

/-- The stream-function assignment of the core bundle. -/
def DynCore.Psi {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ : ℝ} (hin : DynCore Law α g₀ C₀) :
    Fam → Fam := PsiCan hin.Φs hin.EllSol

/-- **The Galerkin a-priori bundle in the primed vocabulary**: the open-quadrant packages
`StarPkgo`/`EllPkgGo` and the open-quadrant limit bound.  This is what replaces
`Work.FTS.Galerkin.DynInputs` on the migrated route. -/
structure DynInputsOpen (Law : Fn → Fn → Prop) (α : ℝ) (g₀ : Fn) (C₀ : ℝ) where
  /-- the fields shared with `DynCore` -/
  core : DynCore Law α g₀ C₀
  Cs : ℝ
  Ce : ℝ
  hΦs : StarPkgo α Cs (core.Φs)
  hEllSol : ∀ g : Fn, GalClass α g → EllPkgGo α Ce g (core.EllSol g)

end Work.FTS.OpenPkg
