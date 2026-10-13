/-
# N4 — the interfaces (contracts) of the nonlinear estimates — **REPAIRED**

This module fixes the hypothesis structures under which the chapter
`Submission/Work/FTS/Nonlinear/` proves the paper's §8 estimates.

## History and why the interface was rewritten

The first version of this file contained a structure `N4RegQ` whose fields were *`RegQ`-level*
statements about derived objects (`RegQ α 4 (L₁₂ g)`, `RegQ α 4 (c·g)`) together with a
general product rule in the weighted `𝒲^{4,∞}`-norm.  Those fields are **false**:

* `RegQ` contains `BdryTraces`, whose angular half at `(0,0)` says
  `sin(2θ)^{1-γ}·f(z,θ)² → 0` with `1 - γ = -α/10 < 0`; this *forces every `RegQ` function of
  `z` alone to vanish identically*, so `RegQ α 4 (fun z θ => L₁₂ g z)` is false as soon as
  `L₁₂ g ≢ 0`.  Machine-checked refutation: `Pieces/NOTES_rowsN0.md` and `Pieces/rowsN0.lean`
  (earlier revision of those files);
* the `𝒲^{4,∞}`-product rule without any boundary-slice regularity is false
  (`Submission/Work/FTS/H2/AuxProdWFalse.lean`, `Submission/Work/FTS/H2/NOTES_prodW_false.md`);
* the field `wtoh`, which carried *no* hypothesis, is false for `ψ z = z^{7/4}/(1+z)^{10}`.

As a consequence `N4RegQ` was uninhabited and every statement under it was vacuously true.

**The repair (this file).**  `N4RegQ` is replaced by `N4Norm`, which carries *norm-level
inequalities only*:

* no field concludes `RegQ α k <derived object>`;
* there is no general product rule in `𝒲^{4,∞}` without regularity of the slices: the field
  `wmul` carries the flat vanishing of one factor on the two angular boundary lines, which is
  what the concrete factors of the `**`-rows (`F_*`, `D_θF_*`) satisfy, and which makes the
  junk values of `supAbs` on the boundary harmless;
* every field is a `SmoothNbhd`-free restatement of a theorem that is **already proved** in the
  tree (named in the docstring of the field) or of an explicitly listed small analytic lemma.

The `IP`-level contract `N4Extra` is *unchanged*: its clauses are satisfiable (`IP ≡ 0`
inhabits it) and it is what makes the pairing side of `pairing_bound_of_rows` work.  In
particular `UnifIP` (the frozen N2 obligation) is *not* enough on its own for an abstract `IP`:
it says nothing about `IP (f·D_θg) g`, so the transport interface `N4Extra` is carried as an
extra hypothesis of `pairing_bound`.

## The main consumption pattern

```
import Submission.Work.FTS.Nonlinear.Interface
open Work.FTS.Nonlin
-- the row estimates take `N4Norm` + the two elliptic packages as hypotheses;
-- the assembly `pairing_bound_of_rows` takes `UnifIP` + `N4Extra` + `RowInputs`.
```
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
-- NOTE: the *proofs* of the fields live in the modules named in the field docstrings
-- (`FTS/H2/HProdQ.lean`, `WProdQ.lean`, `WtoHQ.lean`, `L12HQ.lean`, `L12ZeroQ.lean`,
-- `Spaces/ProductRuleInW.lean`, `Spaces/radial_prod.lean`, `N4Fields/`).  They are deliberately
-- NOT imported here: `FTS/H2/LinfQ.lean` and `FTS/H2/L12densIntegrable.lean` both declare a
-- `Qd` and cannot be imported together (see `FTS/H2/NOTES_H2.md` §7), so importing the proofs
-- into this interface module would make the chapter unbuildable.  Consumers import the proof
-- modules and the interface separately.

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `RegQ`-level contract (N3-fix) — norm-level only -/

/-- **The `RegQ`-level norm facts consumed by N4.**

Every field is an inequality between *norms* of the paper's function spaces (no `IP` occurs, no
field concludes `RegQ` of a derived object), and each is a `SmoothNbhd`-free restatement of a
theorem already in the tree; the constant `Ci` is universal and `α₂` is the range of `α`.  The
factor `α^{-1/2}` is the only permitted loss in `α` (design §2.3, §5 T9): it is
`1/√(γ-1) = √10 α^{-1/2}` with `γ = 1 + α/10`. -/
structure N4Norm (Ci α₂ : ℝ) : Prop where
  pos : 0 < Ci ∧ 0 < α₂
  /-- `ℋ⁴` is closed under products, with the loss `√10 α^{-1/2}` (`HProdQ`, tex 1086). -/
  prod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, RegQ α 4 f → RegQ α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Xn α (fun z θ => f z θ * g z θ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g
  /-- Multiplication by a `𝒲^{4,∞}` function (`WProdQ`, tex 1096). -/
  wprod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.LocData.SmoothQuad f →
    Work.Spaces.WlInfMem α 4 f → RegQ α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Xn α (fun z θ => f z θ * g z θ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g
  /-- `𝒲^{4,∞}` controls `ℋ⁴` through the weight `(z+1)³/z²` (`WtoHQ`, tex 1160). -/
  wtoh : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, Work.FTS.LocData.SmoothQuad f →
    Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) → RegQ α 4 f →
    Xn α f ≤ Ci * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
  /-- `L₁₂` maps the `ℋ⁴`-class into itself, losslessly (`L12HQ`, tex 1119). -/
  l12H : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, RegQ α 4 g → Work.Construction.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
    Xn α (fun z θ => Work.Construction.L12 g z) ≤ Ci * Xn α g
  /-- The zero mode of `L₁₂` is controlled by the `ℋ⁴`-norm (`L12ZeroQ`, tex 1519). -/
  l12zero : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, RegQ α 4 f →
    |Work.Construction.L12 f 0| ≤ Ci * Xn α f
  /-- **The angular moment `FK g = ∫_θ K(θ) g(z,θ) dθ`.**  For `RegQ` data with vanishing zero
  mode, `FK g` is again an `ℋ⁴`-function (it is the radial function `-D_z L₁₂(g) = Qang g 0`,
  the first angular moment of `g`) and is controlled by `Xn α g`.  This is the norm-level half
  of the design's `fk` (§3.2), needed by rows 20, 21, 24 and 25 of the table. -/
  fkH : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, RegQ α 4 g → Work.Construction.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
    Xn α (fun z _ => Work.Construction.FK g z) ≤ Ci * Xn α g
  /-- `z ↦ L₁₂(g)(z)` is differentiable on `(0,∞)` in the interior class; this is the analytic
  input of the four-way split of `N` (design `L-N4.2`; the density `L12dens g` is continuous
  there, `Work.FM.hasDerivAt_L12`).  Needed by `Pieces/splits`. -/
  l12diff : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, Work.FTS.LocData.SmoothQuad g →
    Work.Spaces.HkMem α 4 g → ∀ z ∈ Set.Ioi (0 : ℝ),
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z
  /-- Multiplication by a function of `z` alone is **lossless** in `α` (`radial_prod`,
  design §3.2).  The decay hypotheses are the `z = ∞` clauses of `BdryTraces`, which the
  `RegQ` data supply. -/
  radialMul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (r : ℝ → ℝ) (g : Fn),
    Work.FTS.LocData.SmoothQuad (fun z _ => r z) → Work.FTS.LocData.SmoothQuad g →
    Work.Spaces.HkMem α 4 (fun z _ => r z) → Work.Spaces.HkMem α 4 g →
    (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => r z) z 0)
      Filter.atTop (nhds 0)) →
    (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
    Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
    Xn α (fun z θ => r z * g z θ) ≤ Ci * Xn α (fun z _ => r z) * Xn α g
  /-- Multiplication by an angular profile is lossless in `α` (`HkMul_ang_le`, `Work.Blocks`).

  Two hypotheses are needed and *both* are necessary: `a` is bounded, and its `D_θ`-iterates
  vanish at least like `sin(2θ)` — without the second, `a = 1 + θ^q` (`q < α/5`) breaks the
  conclusion, because the heavy weight `sin(2θ)^{-γ/2}` is unbounded at the boundary.  The
  concrete profiles of the table (`sin(2θ)`, `sin²θ`, `cos(2θ)`, `c2m = cos2θ - sin²θ`) satisfy
  both. -/
  angmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (f : Fn),
    Work.Spaces.SmoothInt (fun _ (θ : ℝ) => a θ) →
    (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
    Xn α (fun z θ => a θ * f z θ) ≤ Ci * Ci * Xn α f
  /-- Multiplication by an angular profile in the `𝒲^{4,∞}`-norm.  **All three hypotheses are
  necessary**: `a` must be *honestly* smooth (`SmoothInt`; `WlInfMem` alone constrains only the
  totalised derivatives and cannot see oscillations at the non-differentiability points —
  see `N4Fields/NOTES_wang_field_false.md`), its `D_θ`-iterates must vanish like `sin(2θ)` (the
  mixed weight `sin(2θ)^{-α/5}/(α+sin 2θ)` is unbounded at the boundary), and `h` must be
  honestly smooth as well. -/
  wang : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (h : Fn),
    Work.Spaces.SmoothInt (fun _ (θ : ℝ) => a θ) → Work.Spaces.SmoothInt h →
    (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
    Work.Spaces.WlInfMem α 4 h →
    Work.Spaces.WlInfMem α 4 (fun z θ => a θ * h z θ) ∧
    Work.Spaces.WlInf α 4 (fun z θ => a θ * h z θ) ≤ Ci * Ci * Work.Spaces.WlInf α 4 h
  /-- Multiplication by a `z`-profile in the `𝒲^{4,∞}`-norm.  As for `wang`, both factors must
  be *honestly* smooth (`SmoothInt`): with only `WlInfMem` the field is false
  (`n4norm_refuted.lean`). -/
  wrad : ∀ α ∈ Set.Ioc 0 α₂, ∀ (φ : ℝ → ℝ) (h : Fn),
    Work.Spaces.SmoothInt (fun z _ => φ z) → Work.Spaces.SmoothInt h →
    Work.Spaces.WlInfMem α 4 (fun z _ => φ z) → Work.Spaces.WlInfMem α 4 h →
    Work.Spaces.WlInfMem α 4 (fun z θ => φ z * h z θ) ∧
    Work.Spaces.WlInf α 4 (fun z θ => φ z * h z θ)
      ≤ Ci * Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h
  /-- **The `𝒲^{4,∞}`-product rule**, with the flat vanishing of one factor on the two angular
  boundary lines which makes the boundary values of `pzIter k` harmless.  This replaces the
  false field `wmul` of the old interface (`H2/AuxProdWFalse.lean`); the pointwise interior
  bound is `H2.prodW_interior_bound`. -/
  wmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g →
    Work.Spaces.WlInfMem α 4 f → Work.Spaces.WlInfMem α 4 g →
    (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ,
      Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) →
    Work.Spaces.WlInfMem α 4 (fun z θ => f z θ * g z θ) ∧
    Work.Spaces.WlInf α 4 (fun z θ => f z θ * g z θ)
      ≤ Ci * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g

/-! ## The `IP`-level contract (N2/N3 for the concrete `IP₄`) -/

/-- **The `IP`-level facts consumed by N4.**

`IP` is the paper's concrete `ℋ⁴` inner product.  The clauses `cs`/`add`/`smul`/`congr` are
the ones of `UnifIP` with the hypothesis `RegQ` required only on the *test function* `g`; the
`RegQ`-hypothesis of the frozen `UnifIP.cs` on the *first* argument is unsatisfiable for the
pieces of `N₀` (see the module docstring of `Defs.lean`).  `t1`–`st` are the transport
estimates of design §3.3 L-N4.5, obtained by summing the per-slot estimates of §H2 over the
slots of `IP₄` (`Work.FTS.H2.Transport1/2/3`, `SpecialTransport`, restated in the interior
class).  This structure is satisfiable (`IP ≡ 0` inhabits it). -/
structure N4Extra (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop where
  pos : 0 < Ct ∧ 0 < α₂
  /-- Cauchy–Schwarz against the `ℋ⁴`-norm. -/
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, RegQ α 4 g → |IP α f g| ≤ Ct * Xn α f * Xn α g
  /-- Additivity in the first argument. -/
  add : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, RegQ α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  /-- Homogeneity in the first argument. -/
  smul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ) (f g : Fn), RegQ α 4 g →
    IP α (fun z θ => c * f z θ) g = c * IP α f g
  /-- Negation in the first argument (a consequence of `smul`, recorded for convenience). -/
  neg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, RegQ α 4 g →
    IP α (fun z θ => -f z θ) g = -IP α f g
  /-- `IP` only depends on the first argument through its values on the open quadrant `Qd`. -/
  congr : ∀ α ∈ Set.Ioc 0 α₂, ∀ f f' g : Fn, RegQ α 4 g →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP α f g = IP α f' g
  /-- The `D_z`-self-pairing, lossless: design §5 T5.  This is `UnifIP.Dz_self` with the
  hypothesis `CoerAdm` relaxed to `RegQ` (the direct integration by parts needs only the
  `ℋ⁴`-finiteness of `g`, not the `L₁₂(g)(0) = 0` zero mode).  It must **not** be routed
  through `Transport3`, whose `α^{-1/2}` loss breaks the bootstrap of design §2.3. -/
  dz : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, RegQ α 4 g → |IP α (Work.Spaces.Dz g) g| ≤ Ct * Xn α g ^ 2
  /-- `T1Q`: transport with `D_θ` and an `ℋ⁴`-coefficient (tex 1119). -/
  t1 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2
  /-- `T2Q`: transport with `D_z` and an `ℋ⁴`-coefficient. -/
  t2 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2
  /-- `T3Q`: transport with `D_z` and a `𝒲^{4,∞}`-coefficient (tex 1213). -/
  t3 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.WlInfMem α 4 f → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g ^ 2
  /-- `T3Q` with `D_θ` and a `𝒲^{4,∞}`-coefficient. -/
  t4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.WlInfMem α 4 f → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g ^ 2
  /-- `STQ`: `SpecialTransport` (tex 1258), the derivative falling on a coefficient which
  vanishes at the angular ends. -/
  st : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.VanishTheta f →
    Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f) → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.pth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) * Xn α g ^ 2

end Work.FTS.Nonlin
