/-
# `OpenPkg/NormFields` — the inhabitation of the primed norm interface `N4Norm'`

The structure `Work.FTS.OpenPkg.N4Norm'` (`Defs.lean`) is the open-quadrant replacement of
`Work.FTS.Nonlin.N4Norm`.  This module reduces its inhabitation to the twelve **field lemmas**,
which are the migration of the twelve backing theorems of the delivered
`Submission/Work/FTS/Nonlinear/n4norm_exists.lean`:

| field | delivered backing theorem | primed field lemma |
|---|---|---|
| `prod` | `Work.FTS.H2.HProdQ` | `Work.FTS.OpenPkg.prod_field` |
| `wprod` | `Work.FTS.H2.WProdQ` | `Work.FTS.OpenPkg.wprod_field` |
| `wtoh` | `Work.FTS.H2.WtoHQ` | `Work.FTS.OpenPkg.wtoh_field` |
| `l12H` | `Work.FTS.H2.L12HQ` | `Work.FTS.OpenPkg.l12H_field` |
| `l12zero` | `Work.FTS.H2.L12ZeroQ` | `Work.FTS.OpenPkg.l12zero_field` |
| `fkH` | `Work.FTS.Nonlinear.N4Fields.fk_field` | `Work.FTS.OpenPkg.fkH_field` |
| `l12diff` | `Work.FM.hasDerivAt_L12` (through `N4Fields/l12diff_field`) | `Work.FTS.OpenPkg.l12diff_field` |
| `radialMul` | `Work.FTS.Nonlinear.RadialProd.radial_prod` | `Work.FTS.OpenPkg.radialMul_field` |
| `angmul` | `Work.FTS.Nonlinear.N4Fields.angmul_field_smoothInt` | `Work.FTS.OpenPkg.angmul_field` |
| `wang` | `Work.FTS.Nonlinear.N4Fields.wang_field_smoothInt` | `Work.FTS.OpenPkg.wang_field` |
| `wrad` | `Work.FTS.Nonlinear.N4Fields.wrad_field_smoothInt` | `Work.FTS.OpenPkg.wrad_field` |
| `wmul` | `Work.FTS.Nonlinear.N4Fields.wmul_field` | `Work.FTS.OpenPkg.wmul_field` |

`N4Norm'_of_fields` proves `N4Norm' Ci α₂` from the twelve fields *at a common constant* `Ci`;
`N4Norm'_exists` takes them in the `∃ C, 0 < C ∧ …` form (which is how each field lemma is stated)
and produces `∃ Ci > 0, N4Norm' Ci α₂`.

## Why each field needs a new proof

The delivered backing theorems are stated in the classes `RegQ` (`SmoothQuad ∧ HkMem ∧
BdryTraces`) and with the norms `WlInf`/`WlInfMem`.  The primed fields are stated in `HQo`
(`SmoothOpen ∧ HkMem`, no boundary traces, smoothness only for `z > 0`) and with `WDp`/`WDMem`.
Neither class implies the other, so the delivered statements cannot be instantiated directly; the
proofs are the same integrations by parts, without the boundary terms that the traces supplied.
The one conversion that *is* available is the norm comparison `WDp ≤ C·WlInf`
(`Work.FTS.OpenPkg.WDp_le_WlInf`): a proved `WlInf`-bound for a concrete object is a `WDp`-bound.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic

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
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The assembly at a common constant -/

/-- **`N4Norm' Ci α₂` from its twelve fields**, each stated with the same constant `Ci`.  This is
the migrated `Work.FTS.Nonlinear.N4Norm` assembly: it is the interface contract, and the twelve
named hypotheses are the lemmas of the table in the module docstring. -/
theorem N4Norm'_of_fields {α₂ Ci : ℝ} (hα₂ : 0 < α₂) (hCi : 0 < Ci)
    (prod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g)
    (wprod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g)
    (wtoh : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) →
      Xn α f ≤ Ci * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ))
    (l12H : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
      Xn α (fun z θ => Work.Construction.L12 g z) ≤ Ci * Xn α g)
    (l12zero : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, HQo α 4 f →
      |Work.Construction.L12 f 0| ≤ Ci * Xn α f)
    (fkH : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
      Xn α (fun z _ => Work.Construction.FK g z) ≤ Ci * Xn α g)
    (l12diff : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z)
    (radialMul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (r : ℝ → ℝ) (g : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 (fun z _ => r z) → Work.Spaces.HkMem α 4 g →
      (∀ b : ℕ, b ≤ 4 → Filter.Tendsto
        (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => r z) z 0) Filter.atTop (nhds 0)) →
      (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
      Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
      Xn α (fun z θ => r z * g z θ) ≤ Ci * Xn α (fun z _ => r z) * Xn α g)
    (angmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (f : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
      Xn α (fun z θ => a θ * f z θ) ≤ Ci * Ci * Xn α f)
    (wang : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (h : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      Work.FTS.EllipticEst.SmoothOpen h →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
      WDMem 4 h →
      WDMem 4 (fun z θ => a θ * h z θ) ∧
      WDp 4 (fun z θ => a θ * h z θ) ≤ Ci * Ci * WDp 4 h)
    (wrad : ∀ α ∈ Set.Ioc 0 α₂, ∀ (φ : ℝ → ℝ) (h : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ => φ z) →
      Work.FTS.EllipticEst.SmoothOpen h →
      WDMem 4 (fun z _ => φ z) → WDMem 4 h →
      WDMem 4 (fun z θ => φ z * h z θ) ∧
      WDp 4 (fun z θ => φ z * h z θ) ≤ Ci * WDp 4 (fun z _ => φ z) * WDp 4 h)
    (wmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      WDMem 4 f → WDMem 4 g →
      (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ,
        Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) →
      WDMem 4 (fun z θ => f z θ * g z θ) ∧
      WDp 4 (fun z θ => f z θ * g z θ) ≤ Ci * WDp 4 f * WDp 4 g) :
    N4Norm' Ci α₂ where
  pos := ⟨hCi, hα₂⟩
  prod := prod
  wprod := wprod
  wtoh := wtoh
  l12H := l12H
  l12zero := l12zero
  fkH := fkH
  l12diff := l12diff
  radialMul := radialMul
  angmul := angmul
  wang := wang
  wrad := wrad
  wmul := wmul

end Work.FTS.OpenPkg
